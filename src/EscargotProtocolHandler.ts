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
  decodeMessage, encodeMessage
} from './EscargotUtils';
import { EscargotDebuggerClient } from './EscargotDebuggerClient';
import { LOG_LEVEL } from './EscargotDebuggerConstants';

export type Pointer = string;
export type ByteCodeOffset = number;
export type LoggerFunction = (message: any, level: number) => void;

export interface ParserStackFrame {
  isFunc: boolean;
  scriptId: number;
  line: number;
  column: number;
  name: string;
  source: string;
  sourceName?: string;
  stack: Array<ParserStackFrame>;
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
  onEvalResult?(subType: number, result: string): void;
  onError?(code: number, message: string): void;
  onResume?(): void;
  onScriptParsed?(message: EscargotMessageScriptParsed): void;
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

export interface EscargotBacktraceResult {
  totalFrames: number;
  backtrace: Array<Breakpoint>;
}

interface FunctionMap {
  [cp: string]: ParsedFunction;
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

export interface EscargotScopeChain {
  name: string;
  variablesReference: number;
  expensive: boolean;
}

export interface EscargotScopeVariable {
  name: string;
  type: string;
  value: string;
}

// abstracts away the details of the protocol
export class EscargotDebugProtocolHandler {
  public debuggerClient?: EscargotDebuggerClient;
  private delegate: EscargotDebugProtocolDelegate;

  // debugger configuration
  private byteConfig: ByteConfig;
  private version: number = 0;
  private functionMap: ProtocolFunctionMap;

  private stack: Array<ParserStackFrame> = [];
  // first element is a dummy because sources is 1-indexed
  private sources: Array<ParsedSource> = [{}];
  // first element is a dummy because lineLists is 1-indexed
  private lineLists: Array<LineFunctionMap> = [[]];
  private source: string = '';
  private sourceData?: Uint8Array;
  private sourceName?: string;
  private sourceNameData?: Uint8Array;
  private functionName?: string;
  private functionNameData?: Uint8Array;
  private functions: FunctionMap = {};
  private newFunctions: FunctionMap = {};
  private backtraceData: EscargotBacktraceResult = {totalFrames : 0, backtrace: []};

  private nextScriptID: number = 1;
  private exceptionString?: string;
  private evalsPending: number = 0;
  private lastBreakpointHit?: Breakpoint;
  private lastBreakpointExact: boolean = true;
  private activeBreakpoints: Array<Breakpoint> = [];
  private nextBreakpointIndex: number = 0;

  private log: LoggerFunction;
  private requestQueue: PendingRequest[];
  private currentRequest: PendingRequest;
  private stopTypeMap: StopTypeMap;
  private lastStopType: number;

  constructor(delegate: EscargotDebugProtocolDelegate, log?: LoggerFunction) {
    this.delegate = delegate;
    this.log = log || <any>(() => {});
    this.stack = [];

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

      [SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_8BIT]: this.onSourceCode8,
      [SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_8BIT_END]: this.onSourceCode8,
      [SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_16BIT]: this.onSourceCode16,
      [SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_16BIT_END]: this.onSourceCode16,

      [SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_8BIT]: this.onSourceCodeName8,
      [SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_8BIT_END]: this.onSourceCodeName8,
      [SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_16BIT]: this.onSourceCodeName16,
      [SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_16BIT_END]: this.onSourceCodeName16,

      [SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_8BIT]: this.onFunctionName8,
      [SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_8BIT_END]: this.onFunctionName8,
      [SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_16BIT]: this.onFunctionName16,
      [SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_16BIT_END]: this.onFunctionName16,

      [SP.SERVER.ESCARGOT_DEBUGGER_BREAKPOINT_LOCATION]: this.onBreakpointList,
      [SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_PTR]: this.onFunctionPtr,
      [SP.SERVER.ESCARGOT_DEBUGGER_BREAKPOINT_HIT]: this.onBreakpointHit,
      [SP.SERVER.ESCARGOT_DEBUGGER_EXCEPTION_HIT]: this.onBreakpointHit,
      [SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE_TOTAL]: this.onBacktraceTotal,

      [SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE_8BIT]: this.onBacktrace,
      [SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE_8BIT_END]: this.onBacktrace,
      [SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE_16BIT]: this.onBacktrace,
      [SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE_16BIT_END]: this.onBacktrace,
    };

    this.requestQueue = [];
    this.currentRequest = null;

    this.stopTypeMap = {
      [SP.CLIENT.ESCARGOT_DEBUGGER_NEXT]: 'step',
      [SP.CLIENT.ESCARGOT_DEBUGGER_STEP]: 'step-in',
      [SP.CLIENT.ESCARGOT_DEBUGGER_CONTINUE]: 'continue',
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
    if (data.length != 2) {
      this.abort('configuration message wrong size');
      return;
    }

    this.byteConfig.pointerSize = data[1];

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

    const frame = this.stack.pop();
    if (!frame) {
      throw new Error('missing parser stack frame');
    }


    const decoded = this.decodeMessage('CII', data, 1);
    frame.line = decoded[1];
    frame.column = decoded[2];
    frame.name = this.functionName;

    const func = new ParsedFunction(decoded[0], frame);
    this.newFunctions[decoded[0]] = func;
    if (this.stack.length > 0) {
      return;
    }

    // FIXME: it seems like this is probably unnecessarily keeping the
    //   whole file's source to this point?
    func.source = this.source.split(/\n/);
    func.sourceName = this.sourceName;
    this.source = '';
    this.sourceName = undefined;

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

    this.log(data.length + "", 4);

    const stackFrame = this.pushStackItem();

    for (let i = 1; i < data.byteLength; i += 8) {
      let decoded = this.decodeMessage('II', data, i);
      this.log(decoded[0] + ":" + decoded[1], 4);
      stackFrame.lines.push(decoded[0]);
      stackFrame.offsets.push(decoded[1]);
    }
    this.log("succ", 4);
  }

  private pushStackItem(): ParserStackFrame {
    let frame = <ParserStackFrame>{
      isFunc: false,
      scriptId: this.nextScriptID,
      line: 1,
      column: 1,
      name: '',
      source: '',
      lines: [],
      offsets: [],
    }

    this.stack.push(frame);
    return frame;
  }

  private addSource(): void {
    this.source = createStringFromArray(this.sourceData);
    this.log(this.source, 4);
    this.sources[this.nextScriptID] = {
      name: this.sourceName,
      source: this.source,
    };
    this.sourceData = undefined;
  }

  public onSourceCode16(data: Uint8Array): void {
    this.logPacket(`Source Code 16bit`, true);
    if (this.evalsPending) {
      return;
    }

    this.sourceData = assembleUint8Arrays(this.sourceData, convert16bitTo8bit(this.byteConfig, data));
    if (data[0] === SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_8BIT_END) {
      this.addSource();
    }
  }

  public onSourceCode8(data: Uint8Array): void {
    this.logPacket(`Source Code 8bit`, true);

    if (this.evalsPending) {
      return;
    }

    this.pushStackItem();
    this.sourceData = assembleUint8Arrays(this.sourceData, data);
    if (data[0] === SP.SERVER.ESCARGOT_DEBUGGER_SOURCE_8BIT_END) {
      this.addSource();
    }
  }

  private finalizeSourceCodeName (): void {
    this.sourceName = createStringFromArray(this.sourceNameData);
    this.sourceNameData = undefined;

    if (this.delegate.onScriptParsed) {
      this.delegate.onScriptParsed({
        'id': this.nextScriptID,
        'name': this.sourceName || '',
        'lineCount': this.source.split(/\n/).length,
      });
    }
  }

  public onSourceCodeName16(data: Uint8Array): void {
    this.logPacket('Source Code Name 16');
    this.sourceNameData = assembleUint8Arrays(this.sourceNameData, convert16bitTo8bit(this.byteConfig, data));

    if (data[0] === SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_16BIT_END) {
      this.finalizeSourceCodeName();
    }
  }

  public onSourceCodeName8(data: Uint8Array): void {
    this.logPacket('Source Code Name 8');
    this.sourceNameData = assembleUint8Arrays(this.sourceNameData, data);

    if (data[0] === SP.SERVER.ESCARGOT_DEBUGGER_FILE_NAME_8BIT_END) {
      this.finalizeSourceCodeName();
    }
  }

  private onFunctionName16(data: Uint8Array): void {
    this.logPacket('Function Name 16');
    this.functionNameData = assembleUint8Arrays(this.functionNameData, convert16bitTo8bit(this.byteConfig, data));
    if (data[0] === SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_16BIT_END) {
      this.functionName = createStringFromArray(this.functionNameData);
      this.functionNameData = undefined;
    }
  }

  private onFunctionName8(data: Uint8Array): void {
    this.logPacket('Function Name 8');
    this.functionNameData = assembleUint8Arrays(this.functionNameData, data);
    if (data[0] === SP.SERVER.ESCARGOT_DEBUGGER_FUNCTION_NAME_8BIT_END) {
      this.functionName = createStringFromArray(this.functionNameData);
      this.functionNameData = undefined;
    }
  }

  public releaseFunction(functionPtr: Pointer): void {
    const func = this.functions[functionPtr];

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

  public onBacktraceTotal(data: Uint8Array): void {
    this.logPacket('Backtrace Total');

    if (data[0] === SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE_TOTAL) {
      this.backtraceData.totalFrames = this.decodeMessage('I', data, 1);
      this.backtraceData.backtrace = [];
    }
  }

  public onBacktrace(data: Uint8Array): EscargotBacktraceResult {
    this.logPacket('Backtrace');

    for (let i = 1; i < data.byteLength; i += this.byteConfig.pointerSize + 4) {
      const breakpointData = this.decodeMessage('CI', data, i);
      this.backtraceData.backtrace.push(this.getBreakpoint(breakpointData).breakpoint);
    }

    if (data[0] === SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE_8BIT_END
        || data[0] === SP.SERVER.ESCARGOT_DEBUGGER_BACKTRACE_16BIT_END) {
      if (this.delegate.onBacktrace) {
        this.delegate.onBacktrace(this.backtraceData);
      }
    }

    return this.backtraceData;
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
    const handler = this.functionMap[message[0]];

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
