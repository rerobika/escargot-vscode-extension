/*
 * Copyright 2018-present Samsung Electronics Co., Ltd. and other contributors
 * Copyright JS Foundation and other contributors, http://js.foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import * as SP from './EscargotProtocolConstants';
import { Breakpoint, ParsedFunction } from './EscargotBreakpoints';
import {
  ByteConfig, createStringFromArray, assembleUint8Arrays, convert16bitTo8bit,
  decodeMessage, encodeMessage, createArrayFromString
} from './EscargotUtils';
import { EscargotDebuggerClient } from './EscargotDebuggerClient';
import { LOG_LEVEL } from './EscargotDebuggerConstants';

export type Pointer = string;
export type ByteCodeOffset = number;
export type LoggerFunction = (message: any, level: number) => void;

export interface ParserFrame {
  isFunction: boolean;
  scriptId: number;
  line: number;
  column: number;
  name: string;
  source: Array<string>;
  sourceName?: string;
  lines: Array<number>;
  offsets: Array<ByteCodeOffset>;
  byteCodePtr?: Pointer;
  firstBreakpointLine?: number;
  firstBreakpointOffset?: ByteCodeOffset;
}

export interface EscargotDebugProtocolDelegate {
  onBacktrace?(backtrace: EscargotBacktraceResult): void;
  onBreakpointHit?(message: EscargotMessageBreakpointHit, stopType: string): void;
  onExceptionHit?(message: EscargotMessageExceptionHit): void;
  onEvalResult?(result: string): void;
  onError?(code: number, message: string): void;
  onResume?(): void;
  onScriptParsed?(message: EscargotMessageScriptParsed): void;
  onOutput?(message: string): void;
  onWaitForSource?(): void;
}

export interface EscargotMessageSource {
  name: string;
  source: string;
}

export interface EscargotMessageScriptParsed {
  id: number;
  name: string;
  lineCount: number;
}

export interface EscargotMessageBreakpointHit {
  breakpoint: Breakpoint;
  exact: boolean;
}

export interface EscargotMessageExceptionHit {
  breakpoint: Breakpoint;
  exact: boolean;
  message: string;
}

export interface EscargotEvalResult {
  subtype: number;
  value: string;
}

interface ProtocolFunctionMap {
  [type: number]: (data: Uint8Array) => void;
}

interface FunctionMap {
  [cp: string]: ParsedFunction;
}

export interface EscargotBacktraceFrame {
  function: ParsedFunction;
  line: number;
  column: number;
  id: number;
}

interface ScopeNameMap {
  [type: number]: string;
}

export interface EscargotBacktraceResult {
  totalFrames: number;
  backtrace: Array<EscargotBacktraceFrame>;
}

interface StringReceivedCb {
  (str: string): any;
}


interface LineFunctionMap {
  // maps line number to an array of functions
  [line: number]: Array<ParsedFunction>;
}

interface ParsedSource {
  name?: string;
  source?: string;
}

interface StopTypeMap {
  [type: number]: string;
}

class PendingRequest {
  public data: Uint8Array;
  public promise: Promise<any>;
  public resolve: (arg?: any) => void;
  public reject: (arg?: any) => void;

  public constructor(data: Uint8Array) {
    this.data = data;
    this.promise = new Promise<any>((resolve, reject) => {
      this.resolve = resolve;
      this.reject = reject;
    });
  }
}

export interface EscargotEvalResult {
  subtype: number;
  value: string;
}

export interface EscargotScopeChain {
  name: string;
  variablesReference: number;
  expensive: boolean;
}

export interface EscargotScopeVariable {
  name: string;
  type: string;
  value: string;
  fullType: number;
  hasValue: boolean;
}

// abstracts away the details of the protocol
export class EscargotDebugProtocolHandler {
  public debuggerClient?: EscargotDebuggerClient;
  private delegate: EscargotDebugProtocolDelegate;

  // debugger configuration
  private byteConfig: ByteConfig;
  private version: number = 0;
  private functionMap: ProtocolFunctionMap;
  private scopeNameMap: ScopeNameMap;

  // first element is a dummy because sources is 1-indexed
  private sources: Array<ParsedSource> = [{}];
  // first element is a dummy because lineLists is 1-indexed
  private lineLists: Array<LineFunctionMap> = [[]];
  private source: string = '';
  private stringBuffer: Uint8Array;
  private stringReceiverMessage: number;
  private stringReceivedCb: StringReceivedCb;
  private sourceName?: string;
  private functionName?: string;
  private lines: Array<number> = [];
  private offsets: Array<ByteCodeOffset> = [];
  private isFunction: boolean = false;
  private functions: FunctionMap = {};
  private newFunctions: FunctionMap = {};
  private scopeMessage?: Array<number> = [];
  private backtraceData: EscargotBacktraceResult = {totalFrames : 0, backtrace: []};
  private backtraceFrames: Map<number, number>;
  private backtraceFrameID: number = 0;
  private variableReferenceID: number = 0;

  private maxMessageSize: number = 0;
  private nextScriptID: number = 1;
  private exceptionString?: string;
  private evalsPending: number = 0;
  private lastBreakpointHit?: Breakpoint;
  private lastBreakpointExact: boolean = true;
  private activeBreakpoints: Array<Breakpoint> = [];
  private nextBreakpointIndex: number = 0;
  private scopeVariables: Array<EscargotScopeVariable> = [];
  private currentScopeVariable: EscargotScopeVariable

  private log: LoggerFunction;
  private requestQueue: PendingRequest[];
  private currentRequest: PendingRequest;
  private stopTypeMap: StopTypeMap;
  private lastStopType: number;

  constructor(delegate: EscargotDebugProtocolDelegate, log?: LoggerFunction) {
    this.delegate = delegate;
    this.log = log || <any>(() => {});
    this.backtraceFrames = new Map<number, number>();

    this.byteConfig = {
      pointerSize: 0,
      littleEndian: true,
    };

    this.functionMap = {
      [SP.SERVER.ESCARGOT_DEBUGGER_VERSION]: this.onVersion,
      [SP.SERVER.ESCARGOT_DEBUGGER_CONFIGURATION]: this.onConfiguration,
      [SP.SERVER.ESCARGOT_DEBUGGER_CLOSE_CONNECTION]: this.onCloseConnection,
      [SP.SERVER.ESCARGOT_DEBUGGER_RELEASE_FUNCTION]: this.onReleaseFunctionPtr,
      [SP.SERVER.ESCARGOT_DEBUGGER_PARSE_NODE]: this.onParseDone,
      [SP.SERVER.ESCARGOT_DEBUGGER_PARSE_ERROR]: this.onParseDone,

      [SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_8BIT]: this.onSourceCode,
      [SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_8BIT_END]: this.onSourceCode,
      [SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_16BIT]: this.onSourceCode,
      [SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_16BIT_END]: this.onSourceCode,

      [SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_8BIT]: this.onFileName,
      [SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_8BIT_END]: this.onFileName,
      [SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_16BIT]: this.onFileName,
      [SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_16BIT_END]: this.onFileName,

      [SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_8BIT]: this.onFunctionName,
      [SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_8BIT_END]: this.onFunctionName,
      [SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_16BIT]: this.onFunctionName,
      [SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_16BIT_END]: this.onFunctionName,

      [SP.SERVER.ESCARGOT_DEBUGGER_BREAKPOINT_LOCATION]: this.onBreakpointList,
      [SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_PTR]: this.onFunctionPtr,
      [SP.SERVER.ESCARGOT_DEBUGGER_BREAKPOINT_HIT]: this.onBreakpointHit,
      [SP.SERVER.ESCARGOT_DEBUGGER_EXCEPTION_HIT]: this.onBreakpointHit,

      [SP.SERVER.ESCARGOT_DEBUGGER_EVAL_RESULT_8BIT]: this.onEvalResult,
      [SP.SERVER.ESCARGOT_DEBUGGER_EVAL_RESULT_8BIT_END]: this.onEvalResult,
      [SP.SERVER.ESCARGOT_DEBUGGER_EVAL_RESULT_16BIT]: this.onEvalResult,
      [SP.SERVER.ESCARGOT_DEBUGGER_EVAL_RESULT_16BIT_END]: this.onEvalResult,

      [SP.SERVER.ESCARGOT_DEBUGGER_EVAL_FAILED_8BIT]: this.onEvalFailed,
      [SP.SERVER.ESCARGOT_DEBUGGER_EVAL_FAILED_8BIT_END]: this.onEvalFailed,
      [SP.SERVER.ESCARGOT_DEBUGGER_EVAL_FAILED_16BIT]: this.onEvalFailed,
      [SP.SERVER.ESCARGOT_DEBUGGER_EVAL_FAILED_16BIT_END]: this.onEvalFailed,

      [SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE_TOTAL]: this.onBacktraceTotal,
      [SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE]: this.onBacktrace,
      [SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE_END]: this.onBacktraceEnd,

      [SP.SERVER.ESCARGOT_DEBUGGER_SCOPE_CHAIN]: this.onScopeChain,
      [SP.SERVER.ESCARGOT_DEBUGGER_SCOPE_CHAIN_END]: this.onScopeChainEnd,
      [SP.SERVER.ESCARGOT_DEBUGGER_MESSAGE_VARIABLE]: this.onScopeVariable,

      [SP.SERVER.ESCARGOT_DEBUGGER_STRING_8BIT]: this.onMessageString,
      [SP.SERVER.ESCARGOT_DEBUGGER_STRING_8BIT_END]: this.onMessageString,
      [SP.SERVER.ESCARGOT_DEBUGGER_STRING_16BIT]: this.onMessageString,
      [SP.SERVER.ESCARGOT_DEBUGGER_STRING_16BIT_END]: this.onMessageString,
      [SP.SERVER.ESCARGOT_DEBUGGER_MESSAGE_PRINT]: this.onPrint,
      [SP.SERVER.ESCARGOT_DEBUGGER_MESSAGE_EXCEPTION]: this.onException,
      [SP.SERVER.ESCARGOT_DEBUGGER_MESSAGE_EXCEPTION_BACKTRACE]: this.onBacktrace,
    };

    this.scopeNameMap = {
      [SP.ESCARGOT_DEBUGGER_SCOPE_TYPE.ESCARGOT_DEBUGGER_SCOPE_GLOBAL]: "Global Environment",
      [SP.ESCARGOT_DEBUGGER_SCOPE_TYPE.ESCARGOT_DEBUGGER_SCOPE_FUNCTION]: "Function Environment",
      [SP.ESCARGOT_DEBUGGER_SCOPE_TYPE.ESCARGOT_DEBUGGER_SCOPE_DECLARATIVE]: "Declarative Environment",
      [SP.ESCARGOT_DEBUGGER_SCOPE_TYPE.ESCARGOT_DEBUGGER_SCOPE_OBJECT]: "Object Environment",
      [SP.ESCARGOT_DEBUGGER_SCOPE_TYPE.ESCARGOT_DEBUGGER_SCOPE_MODULE]: "Module Environment",
      [SP.ESCARGOT_DEBUGGER_SCOPE_TYPE.ESCARGOT_DEBUGGER_SCOPE_UNKNOWN]: "Unknown Environment",
    }

    this.requestQueue = [];
    this.currentRequest = null;

    this.stopTypeMap = {
      [SP.CLIENT.ESCARGOT_DEBUGGER_NEXT]: 'step',
      [SP.CLIENT.ESCARGOT_DEBUGGER_STEP]: 'step-in',
      [SP.CLIENT.ESCARGOT_DEBUGGER_FINISH]: 'step-out',
      [SP.CLIENT.ESCARGOT_DEBUGGER_CONTINUE]: 'continue',
      [SP.CLIENT.ESCARGOT_DEBUGGER_STOP]: 'pause',
    };
    this.lastStopType = null;
  }

  // FIXME: this lets test suite run for now
  public unused(): void {
    // tslint:disable-next-line no-unused-expression
    this.lastBreakpointExact;
  }

  public stepOver(): Promise<any> {
    return this.resumeExec(SP.CLIENT.ESCARGOT_DEBUGGER_NEXT);
  }

  public stepInto(): Promise<any> {
    return this.resumeExec(SP.CLIENT.ESCARGOT_DEBUGGER_STEP);
  }

  public stepOut(): Promise<any> {
    return this.resumeExec(SP.CLIENT.ESCARGOT_DEBUGGER_FINISH);
  }

  public pause(): Promise<any> {
    if (this.lastBreakpointHit) {
      return Promise.reject(new Error('attempted pause while at breakpoint'));
    }

    this.lastStopType = SP.CLIENT.ESCARGOT_DEBUGGER_STOP;
    return this.resumeExec(SP.CLIENT.ESCARGOT_DEBUGGER_STEP);
  }

  public resume(): Promise<any> {
    return this.resumeExec(SP.CLIENT.ESCARGOT_DEBUGGER_CONTINUE);
  }

  public getPossibleBreakpoints(scriptId: number, startLine: number, endLine?: number): Array<Breakpoint> {
    const array = [];
    const lineList = this.lineLists[scriptId];
    for (const line in lineList) {
      const linenum = Number(line);
      if (linenum >= startLine) {
        if (!endLine || linenum <= endLine) {
          for (const func of lineList[line]) {
            array.push(func.lines[line]);
          }
        }
      }
    }
    return array;
  }

  public getSources(): ParsedSource[] {
    // The first element is a dummy because sources is 1-indexed
    return this.sources.slice(1);
  }

  public getSource(scriptId: number): string {
    if (scriptId < this.sources.length) {
      return this.sources[scriptId].source || '';
    }
    return '';
  }

  private decodeMessage(format: string, message: Uint8Array, offset: number): any {
    return decodeMessage(this.byteConfig, format, message, offset);
  }

  public onVersion(data: Uint8Array): void {
    this.logPacket('Version');
    if (data.length != 6) {
      this.abort('version message wrong size');
      return;
    }

    this.byteConfig.littleEndian = Boolean(data[1]);
    this.version = this.decodeMessage('I', data, 2)[0];

    if (this.version !== SP.ESCARGOT_DEBUGGER_VERSION) {
      this.abort(`incorrect target debugger version detected: ${this.version} expected: ${SP.ESCARGOT_DEBUGGER_VERSION}`);
    }
  }

  public onConfiguration(data: Uint8Array): void {
    this.logPacket('Configuration');
    if (data.length != 3) {
      this.abort('configuration message wrong size');
      return;
    }

    this.maxMessageSize = data[1];
    console.log(this.maxMessageSize);
    this.byteConfig.pointerSize = data[2];

    if (this.byteConfig.pointerSize !== 4
        && this.byteConfig.pointerSize !== 8) {
      this.abort(`unsupported pointer size: ${this.byteConfig.pointerSize}`);
    }
  }

  public onFunctionPtr(data: Uint8Array): void {
    this.logPacket('Function Ptr', true);
    if (this.evalsPending) {
      return;
    }


    const decoded = this.decodeMessage('CII', data, 1);

    const frame = <ParserFrame> {
      isFunction: this.isFunction,
      scriptId: this.nextScriptID - 1,
      line: decoded[1],
      column: decoded[2],
      name: this.functionName,
      source: this.source.split(/\n/),
      sourceName: this.sourceName,
      lines: this.lines,
      offsets: this.offsets,
    }

    const func = new ParsedFunction(decoded[0], frame);
    this.newFunctions[decoded[0]] = func;

    // FIXME: it seems like this is probably unnecessarily keeping the
    //   whole file's source to this point?
    func.source = this.source.split(/\n/);

    const lineList: LineFunctionMap = {};
    for (const p in this.newFunctions) {
      const func = this.newFunctions[p];
      this.functions[p] = func;

      for (const i in func.lines) {
        // map line numbers to functions for this source
        if (i in lineList) {
          lineList[i].push(func);
        } else {
          lineList[i] = [func];
        }
      }
    }
    this.lineLists.push(lineList);
    this.lines = [];
    this.offsets = [];
    this.nextScriptID++;
    this.newFunctions = {};
  }

  private onParseDone(data: Uint8Array): void {
    this.logPacket('Parse Function');
    return;
  }

  public onBreakpointList(data: Uint8Array): void {
    this.logPacket('Breakpoint List', true);

    if (this.evalsPending) {
      return;
    }

    if (data.byteLength % 8 !== 1 || data.byteLength < 1 + 8) {
      throw new Error('unexpected breakpoint list message length');
    }

    for (let i = 1; i < data.byteLength; i += 8) {
      let decoded = this.decodeMessage('II', data, i);
      this.log(decoded[0] + ":" + decoded[1], 4);
      this.lines.push(decoded[0]);
      this.offsets.push(decoded[1]);
    }
  }

  public receiveString(data: Uint8Array): void {
    const is8bit = (data[0] - this.stringReceiverMessage) < 2;
    const isEnd = ((data[0] - this.stringReceiverMessage) & 0x01) == 1;

    if (is8bit) {
      this.stringBuffer = assembleUint8Arrays(this.stringBuffer, data);
    } else {
      this.stringBuffer = assembleUint8Arrays(this.stringBuffer, convert16bitTo8bit(this.byteConfig, data));
    }

    if (isEnd) {
      const str = createStringFromArray(this.stringBuffer);
      this.stringReceiverMessage = NaN;
      this.stringBuffer = undefined;
      const currentStringReceiveCb = this.stringReceivedCb;
      this.stringReceivedCb(str);
      if (currentStringReceiveCb == this.stringReceivedCb) {
        this.stringReceivedCb = null;
      }
    }
  }

  private onSourceCodeEnd(str: string): void {
    this.source = str;
    this.functionName = 'global';
    this.isFunction = false;
  }

  public onSourceCode(data: Uint8Array): void {
    this.logPacket(`Source Code`, true);

    if (this.evalsPending) {
      return;
    }

    this.stringReceiverMessage = SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_8BIT;
    this.stringReceivedCb = this.onSourceCodeEnd;
    this.receiveString(data);
  }

  private onFileNameEnd (str: string): void {
    this.sourceName = str;
    this.sources[this.nextScriptID] = {
      name: this.sourceName,
      source: this.source,
    };

    if (this.delegate.onScriptParsed) {
      this.delegate.onScriptParsed({
        'id': this.nextScriptID,
        'name': this.sourceName || '',
        'lineCount': this.source.split(/\n/).length,
      });
    }

    this.nextScriptID++;
  }

  public onFileName(data: Uint8Array): void {
    this.logPacket('File Name');

    this.stringReceiverMessage = SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_8BIT;
    this.stringReceivedCb = this.onFileNameEnd;
    this.receiveString(data);
  }

  private onFunctionNameEnd(str: string): void {
    this.functionName = str;
    this.isFunction = true;
  }

  private onFunctionName(data: Uint8Array): void {
    this.logPacket('Function Name');

    this.stringReceiverMessage = SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_8BIT;
    this.stringReceivedCb = this.onFunctionNameEnd;
    this.receiveString(data);
  }

  public releaseFunction(functionPtr: Pointer): void {
    const func = this.functions[functionPtr];

    if (!func) {
      return;
    }

    const lineList = this.lineLists[func.scriptId];
    for (const i in func.lines) {
      const array = lineList[i];
      const index = array.indexOf(func);
      array.splice(index, 1);

      const breakpoint = func.lines[i];
      if (breakpoint.activeIndex >= 0) {
        delete this.activeBreakpoints[breakpoint.activeIndex];
      }
    }

    delete this.functions[functionPtr];
  }

  private onReleaseFunctionPtr(data: Uint8Array): void {
    this.logPacket('Release Function Pointer', true);
    if (!this.evalsPending) {
      const functionPtr = this.decodeMessage('C', data, 1)[0];
      if (functionPtr in this.newFunctions) {
        delete this.newFunctions[functionPtr];
      } else {
        this.releaseFunction(functionPtr);
      }
    }

    // just patch up incoming message
    data[0] = SP.CLIENT.ESCARGOT_DEBUGGER_FUNCTION_RELEASED;
    this.sendSimpleRequest(data);
  }

  private getBreakpoint(breakpointData: Array<number>): EscargotMessageBreakpointHit {
    const func = this.functions[breakpointData[0]];
    const offset = breakpointData[1];

    if (offset in func.offsets) {
      return {
        breakpoint: func.offsets[offset],
        exact: true,
      };
    }

    if (offset < func.firstBreakpointOffset) {
      return {
        breakpoint: func.offsets[func.firstBreakpointOffset],
        exact: true,
      };
    }

    let nearestOffset = -1;
    for (const currentOffset in func.offsets) {
      const current = Number(currentOffset);
      if ((current <= offset) && (current > nearestOffset)) {
        nearestOffset = current;
      }
    }

    return {
      breakpoint: func.offsets[nearestOffset],
      exact: false,
    };
  }

  public onBreakpointHit(data: Uint8Array): void {
    if (data[0] === SP.SERVER.ESCARGOT_DEBUGGER_BREAKPOINT_HIT) {
      this.logPacket('Breakpoint Hit');
    } else {
      this.logPacket('Exception Hit');
    }
    const breakpointData = this.decodeMessage('CI', data, 1);
    const breakpointRef = this.getBreakpoint(breakpointData);
    const breakpoint = breakpointRef.breakpoint;

    this.lastBreakpointHit = breakpoint;
    this.lastBreakpointExact = breakpointRef.exact;

    let breakpointInfo = '';
    if (breakpoint.activeIndex >= 0) {
      breakpointInfo = `breakpoint:${breakpoint.activeIndex} `;
    }

    const atAround = breakpointRef.exact ? 'at' : 'around';
    this.log(`Stopped ${atAround} ${breakpointInfo}${breakpoint}`, LOG_LEVEL.PROTOCOL);

    if (data[0] === SP.SERVER.ESCARGOT_DEBUGGER_EXCEPTION_HIT) {
      this.log('Exception throw detected', LOG_LEVEL.ERROR);
      if (this.exceptionString) {
        this.log(`Exception hint: ${this.exceptionString}`, LOG_LEVEL.ERROR);
      }

      if (this.delegate.onExceptionHit) {
        this.delegate.onExceptionHit({
          'breakpoint': breakpoint,
          'exact': breakpointRef.exact,
          'message': this.exceptionString,
        });
        this.exceptionString = undefined;
        return;
      }
    }

    if (this.delegate.onBreakpointHit) {
      const stopTypeText = this.stopTypeMap[this.lastStopType] || 'entry';
      const stopType = `${breakpoint.activeIndex === -1 ? 'inactive ' : ''}breakpoint (${stopTypeText})`;
      this.delegate.onBreakpointHit(breakpointRef, stopType);
    }

    this.lastStopType = null;
  }

  public onScopeChain(data: Uint8Array): void {
    this.logPacket('ScopeChain');

    for (let i = 1; i < data.byteLength; i++) {
      this.scopeMessage.push(data[i]);
    }
  }

  public onScopeChainEnd(data: Uint8Array): Array<EscargotScopeChain> {
    this.logPacket('ScopeChainEnd');

    for (let i = 1; i < data.byteLength; i++) {
      this.scopeMessage.push(data[i]);
    }

    const scopes: Array<EscargotScopeChain> = [];
    for (let i = 0; i < this.scopeMessage.length; i++) {
       if (this.scopeMessage[i] > SP.ESCARGOT_DEBUGGER_SCOPE_TYPE.ESCARGOT_DEBUGGER_SCOPE_UNKNOWN) {
        throw new Error('Invalid scope chain type!');
      }

      scopes.push({name: this.scopeNameMap[this.scopeMessage[i]],
                   variablesReference: this.variableReferenceID++,
                   expensive: true});
    }
    this.scopeMessage = [];

    return scopes;
  }

  public onScopeVariableValue(str: string) {
    this.logPacket('ScopeVariable Value');
    if (this.currentScopeVariable.fullType & SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_LONG_VALUE) {
      this.currentScopeVariable.value += "...";
    }

    this.currentScopeVariable.value = str;
    this.scopeVariables.push(this.currentScopeVariable);
  }

  public onScopeVariableName(str: string) {
    this.logPacket('ScopeVariable Name');
    this.currentScopeVariable.name = str;
    if (this.currentScopeVariable.fullType & SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_LONG_NAME) {
      this.currentScopeVariable.name += "...";
    }

    if (!this.currentScopeVariable.hasValue) {
      this.scopeVariables.push(this.currentScopeVariable);
      return;
    }

    this.stringReceivedCb = this.onScopeVariableValue;
  }

  public onScopeVariable(data: Uint8Array): any {
    this.logPacket('ScopeVariables');

    this.currentScopeVariable = {name: '',
                                 type: '',
                                 value: '',
                                 fullType: data[1],
                                 hasValue: false};

    let variableType = this.currentScopeVariable.fullType & 0x3f;

    if (this.scopeVariables.length >= 34) {
      this.logPacket('5');
    }

    switch (variableType) {
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_END: {
        let scopeVariables = [];
        Object.assign (scopeVariables, this.scopeVariables);
        this.scopeVariables = [];
        return scopeVariables;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_UNACCESSIBLE: {
        this.currentScopeVariable.type = "unaccessible";
        break;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_UNDEFINED: {
        this.currentScopeVariable.type = "undefined";
        break;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_NULL: {
        this.currentScopeVariable.type = "null";
        break;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_TRUE: {
        this.currentScopeVariable.type = "true";
        break;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_FALSE: {
        this.currentScopeVariable.type = "false";
        break;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_NUMBER: {
        this.currentScopeVariable.type = "number";
        this.currentScopeVariable.hasValue = true;
        break;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_STRING: {
        this.currentScopeVariable.type = "string";
        this.currentScopeVariable.hasValue = true;
        break;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_SYMBOL: {
        this.currentScopeVariable.type = "Symbol:";
        this.currentScopeVariable.hasValue = true;
        break;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_OBJECT: {
        this.currentScopeVariable.type = "object";
        break;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_ARRAY: {
        this.currentScopeVariable.type = "array";
        break;
      }
      case SP.ESCARGOT_DEBUGGER_SCOPE_VARIABLES.ESCARGOT_DEBUGGER_VARIABLE_FUNCTION: {
        this.currentScopeVariable.type = "function";
        break;
      }
      default: {
        throw Error ("Invalid scope variable type");
      }
    }

    this.stringReceivedCb = this.onScopeVariableName;
  }

  public onPrintEnd(str: string): void {
    if (this.delegate.onOutput) {
      this.delegate.onOutput(str);
    }
  }

  public onPrint(data: Uint8Array): void {
    this.logPacket('Print');
    this.stringReceivedCb = this.onPrintEnd;
  }

  public onExceptionEnd(str: string): void {
    if (this.delegate.onOutput) {
      this.delegate.onOutput(`Exception: ${str}`);
    }
  }

  public onException(data: Uint8Array): void {
    this.logPacket('Exception');
    this.stringReceivedCb = this.onExceptionEnd;
  }

  public onMessageStringEnd(str: string): void {
    this.abort('Uncaught message string!');
  }

  public onMessageString(data: Uint8Array): void {
    this.logPacket('Message string');

    this.stringReceiverMessage = SP.SERVER.ESCARGOT_DEBUGGER_STRING_8BIT;
    if (!this.stringReceivedCb) {
      this.abort('Uncaught message string!');
    }
    this.receiveString(data);
  }

  public onBacktraceTotal(data: Uint8Array): void {
    this.logPacket('Backtrace Total');

    this.backtraceData.totalFrames = this.decodeMessage('I', data, 1);
    this.backtraceData.backtrace = [];
  }

  private decodeBackTraceFrame(data: Uint8Array) : void {
    for (let i = 1;  i < data.byteLength; i += this.byteConfig.pointerSize + 8) {
      const backtraceData = this.decodeMessage('CII', data, i);
      let frame = <EscargotBacktraceFrame>{
        function: this.functions[backtraceData[0]],
        line: backtraceData[1],
        column: backtraceData[2],
        id: this.backtraceFrameID++,
      }
      this.backtraceData.backtrace.push(frame);
      this.backtraceFrames.set(frame.id, this.backtraceData.totalFrames - this.backtraceData.backtrace.length);
    }
  }

  public resolveTraceFrameDepthByID(id: number) : number {
    return this.backtraceFrames.get(id);
  }

  public onBacktraceEnd(data: Uint8Array): EscargotBacktraceResult {
    this.logPacket('Backtrace End');
    this.decodeBackTraceFrame(data);

    if (this.delegate.onBacktrace) {
      this.delegate.onBacktrace(this.backtraceData);
    }

    return this.backtraceData;
  }

  public onBacktrace(data: Uint8Array): void {
    this.logPacket('Backtrace');
    this.decodeBackTraceFrame(data);
  }

  public onEvalFailedEnd(str: string): string {
    if (this.delegate.onEvalResult) {
      this.delegate.onEvalResult(str);
    }

    this.evalsPending--;
    return `Exception: ${str}`;
  }

  public onEvalFailed(data: Uint8Array): void {
    this.logPacket('Eval Failed');

    this.stringReceiverMessage = SP.SERVER.ESCARGOT_DEBUGGER_EVAL_FAILED_8BIT;
    this.stringReceivedCb = this.onEvalFailedEnd;
    this.receiveString(data);
  }

  public onEvalResultEnd(str: string): string {
    if (this.delegate.onEvalResult) {
      this.delegate.onEvalResult(str);
    }

    this.evalsPending--;
    return str;
  }

  public onEvalResult(data: Uint8Array): void {
    this.logPacket('Eval Result');

    this.stringReceiverMessage = SP.SERVER.ESCARGOT_DEBUGGER_EVAL_RESULT_8BIT;
    this.stringReceivedCb = this.onEvalResultEnd;
    this.receiveString(data);
  }

  public onMessage(message: Uint8Array): void {
    if (message.byteLength < 1) {
      this.abort('message too short');
      return;
    }

    if (this.version === 0) {
      if (message[0] !== SP.SERVER.ESCARGOT_DEBUGGER_VERSION) {
        this.abort('the first message must be configuration');
        return;
      }
    }

    const request = this.currentRequest;
    let handler = this.functionMap[message[0]];

    if (!isNaN(this.stringReceiverMessage)) {
      handler = this.receiveString;
    }

    if (handler) {
      const result = handler.call(this, message) || false;
      if (request && result) {
        request.resolve(result);

        // Process the queued requests.
        if (this.requestQueue.length > 0) {
          const newRequest = this.requestQueue.shift();

          if (!this.submitRequest(newRequest)) {
            newRequest.reject('Failed to submit request.');
          }
        } else {
          this.currentRequest = null;
        }
      }
    } else {
      if (request) request.reject(`unhandled protocol message type: ${message[0]}`);
      this.abort(`unhandled protocol message type: ${message[0]}`);
    }
  }
  public onCloseConnection(): void {
    this.logPacket('Close connection');

    this.debuggerClient.disconnect();
  }

  public getLastBreakpoint(): Breakpoint {
    return this.lastBreakpointHit;
  }

  public getScriptIdByName(name: string): number {
    const index = this.sources.findIndex(s => s.name && s.name.endsWith(name));
    if (index > 0) return index;
    throw new Error('no such source');
  }

  public getActiveBreakpoint(breakpointId: number): Breakpoint {
    return this.activeBreakpoints[breakpointId];
  }

  public getActiveBreakpointsByScriptId(scriptId: number): Breakpoint[] {
    return this.activeBreakpoints.filter(b => b.scriptId === scriptId);
  }

  public getActiveFunctionBreakpointsByScriptId(scriptId: number): Breakpoint[] {
    return this.getPossibleFunctionBreakpointsByScriptId(scriptId).filter(b => b.activeIndex !== -1);
  }

  public getInactiveFunctionBreakpointsByScriptId(scriptId: number): Breakpoint[] {
    return this.getPossibleFunctionBreakpointsByScriptId(scriptId).filter(b => b.activeIndex === -1);
  }

  public getPossibleFunctionBreakpointsByScriptId(scriptId: number): Breakpoint[] {
    if (scriptId <= 0 || scriptId >= this.lineLists.length) {
      throw new Error('invalid script id');
    }

    const keys: string[] = Object.keys(this.functions).filter(f => this.functions[f].scriptId === scriptId);
    const bps: Breakpoint[] = keys.map(key => this.functions[key].lines[Object.keys(this.functions[key].lines)[0]]);

    return bps.length ? bps.filter(b => b.func.name !== '') : [];
  }

  public findBreakpoint(scriptId: number, line: number, column: number = 0): Breakpoint {
    if (scriptId <= 0 || scriptId >= this.lineLists.length) {
      throw new Error('invalid script id');
    }

    const lineList = this.lineLists[scriptId];
    if (!lineList[line]) {
      throw new Error(`no breakpoint found for line: ${line}`);
    }

    for (const func of lineList[line]) {
      const breakpoint = func.lines[line];
      // TODO: when we start handling columns we would need to distinguish them
      return breakpoint;
    }

    throw new Error('no breakpoint found');
  }

  public updateBreakpoint(breakpoint: Breakpoint, enable: boolean): Promise<void> {
    let breakpointId;

    if (enable) {
      if (breakpoint.activeIndex !== -1) {
        return Promise.reject(new Error('breakpoint already enabled'));
      }
      breakpointId = breakpoint.activeIndex = this.nextBreakpointIndex++;
      this.activeBreakpoints[breakpointId] = breakpoint;
    } else {
      if (breakpoint.activeIndex === -1) {
        return Promise.reject(new Error('breakpoint already disabled'));
      }
      breakpointId = breakpoint.activeIndex;
      delete this.activeBreakpoints[breakpointId];
      breakpoint.activeIndex = -1;
    }

    return this.sendSimpleRequest(encodeMessage(this.byteConfig, 'BBCI', [
      SP.CLIENT.ESCARGOT_DEBUGGER_UPDATE_BREAKPOINT,
      Number(enable),
      breakpoint.func.functionPtr,
      breakpoint.offset,
    ]));
  }

  public sendString (messageType: number, str: string) {
    const array = createArrayFromString(this.byteConfig, str);

    const size = array.length;
    let messageHeader = 1 + 4;

    if (array.some(x => x > 0xff)) {
      messageType += 2;
    }

    let maxFragment = Math.min(this.maxMessageSize - messageHeader, size);

    let message = encodeMessage(this.byteConfig, "BI", [messageType, size]);

    if (size == maxFragment)
    {
      return this.sendRequest(Uint8Array.from([...message, ...array]));
    }

    let request = this.sendRequest(Uint8Array.from([...message, ...array.slice(0, maxFragment)]));
    let offset = maxFragment;
    messageHeader = 1;
    messageType += 1;

    maxFragment = this.maxMessageSize - messageHeader;

    while (offset < size) {
      let nextFragment = Math.min(maxFragment, size - offset);

      message = encodeMessage(this.byteConfig, "BB", [messageType]);

      let prevOffset = offset;
      offset += nextFragment;

      request = this.sendRequest(Uint8Array.from([...message, ...array.slice(prevOffset, offset)]));
    }

    return request;
  }

  public evaluate(expression: string, index: number): Promise<any> {
    if (!this.lastBreakpointHit) {
      return Promise.reject(new Error('attempted eval while not at breakpoint'));
    }

    this.evalsPending++;

    return this.sendString(SP.CLIENT.ESCARGOT_DEBUGGER_EVAL_8BIT_START, expression)
  }

  public requestScopes(): Promise<any> {
    if (!this.lastBreakpointHit) {
      return Promise.reject(new Error('scope chain not allowed while app running'));
    }

    return this.sendRequest(encodeMessage(this.byteConfig, 'B',
                                          [SP.CLIENT.ESCARGOT_DEBUGGER_GET_SCOPE_CHAIN]));
  }

  public requestVariables(level?: number): Promise<any> {
    if (!this.lastBreakpointHit) {
      return Promise.reject(new Error('scope variables not allowed while app running'));
    }

    return this.sendRequest(encodeMessage(this.byteConfig, 'BI',
                                          [SP.CLIENT.ESCARGOT_DEBUGGER_GET_SCOPE_VARIABLES,
                                          level]));

  }

  public requestBacktrace(start?: number, levels?: number): Promise<any> {
    if (start === undefined)
      start = 0;
    if (levels === undefined)
      levels = 0;

    if (!this.lastBreakpointHit) {
      return Promise.reject(new Error('backtrace not allowed while app running'));
    }

    return this.sendRequest(encodeMessage(this.byteConfig, 'BIIB',
                                          [SP.CLIENT.ESCARGOT_DEBUGGER_GET_BACKTRACE,
                                           start,
                                           start + levels,
                                           1]));
  }

  logPacket(description: string, ignorable: boolean = false) {
    // certain packets are ignored while evals are pending
    const ignored = (ignorable && this.evalsPending) ? 'Ignored: ' : '';
    this.log(`${ignored}${description}`, LOG_LEVEL.PROTOCOL);
  }

  private abort(message: string) {
    debugger;
    if (this.delegate.onError) {
      this.log(`Abort: ${message}`, LOG_LEVEL.ERROR);
      this.delegate.onError(0, message);
    }
  }

  private resumeExec(code: number): Promise<any> {
    if (!this.lastBreakpointHit) {
      return Promise.reject(new Error('attempted resume while not at breakpoint'));
    }

    this.lastBreakpointHit = undefined;
    this.lastStopType = code;
    const result = this.sendSimpleRequest(encodeMessage(this.byteConfig, 'B', [code]));

    if (this.delegate.onResume) {
      this.delegate.onResume();
    }

    return result;
  }

  private sendRequest(data: Uint8Array): Promise<any> {
    const request = new PendingRequest(data);

    if (this.currentRequest !== null) {
      this.requestQueue = [...this.requestQueue, request];
    } else {
      if (!this.submitRequest(request)) {
        return Promise.reject(new Error('Failed to submit request.'));
      }
    }

    return request.promise;
  }

  private sendSimpleRequest(data: Uint8Array): Promise<any> {
    const request = new PendingRequest(data);

    if (!this.submitRequest(request, true)) {
      return Promise.reject(new Error('Failed to submit request.'));
    }

    return Promise.resolve();
  }

  private submitRequest(request: PendingRequest, simple: boolean = false): boolean {
    if (!this.debuggerClient!.send(request.data)) return false;
    if (!simple) this.currentRequest = request;
    return true;
  }

}
