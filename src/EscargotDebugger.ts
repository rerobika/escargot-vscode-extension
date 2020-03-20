/*
 * Copyright 2018-present Samsung Electronics Co., Ltd. and other contributors
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

'use strict';

import {
  DebugSession, InitializedEvent, OutputEvent, Thread, Source,
  StoppedEvent, StackFrame, TerminatedEvent, ErrorDestination
} from 'vscode-debugadapter';
import { DebugProtocol } from 'vscode-debugprotocol';
import * as Fs from 'fs';
import * as Path from 'path';
import * as Util from 'util';
import { IAttachRequestArguments, ILaunchRequestArguments, TemporaryBreakpoint } from './EscargotDebuggerInterfaces';
import { EscargotDebuggerClient, EscargotDebuggerOptions } from './EscargotDebuggerClient';
import {
  EscargotDebugProtocolDelegate, EscargotDebugProtocolHandler, EscargotMessageScriptParsed,
  EscargotMessageExceptionHit, EscargotMessageBreakpointHit, EscargotBacktraceResult
} from './EscargotProtocolHandler';
import { Breakpoint } from './EscargotBreakpoints';
import { LOG_LEVEL } from './EscargotDebuggerConstants';

class EscargotDebugSession extends DebugSession {

  // We don't support multiple threads, so we can use a hardcoded ID for the default thread
  private static THREAD_ID = 1;

  private _attachArgs: IAttachRequestArguments;
  private _launchArgs: ILaunchRequestArguments;
  private _debugLog: number = 0;
  private _debuggerClient: EscargotDebuggerClient;
  private _protocolhandler: EscargotDebugProtocolHandler;

  public constructor() {
    super();

    // The debugger uses zero-based lines and columns.
    this.setDebuggerLinesStartAt1(false);
    this.setDebuggerColumnsStartAt1(false);
  }

  protected threadsRequest(response: DebugProtocol.ThreadsResponse): void {
    // Runtime supports now threads so just return a default thread.
    response.body = {
      threads: [
        new Thread(EscargotDebugSession.THREAD_ID, 'Main Thread')
      ]
    };
    this.sendResponse(response);
  }

  /**
   * The 'initialize' request is the first request called by the frontend
   * to interrogate the debug adapter about the features it provides.
   */
  protected initializeRequest(
    response: DebugProtocol.InitializeResponse, args: DebugProtocol.InitializeRequestArguments
  ): void {
    // This debug adapter implements the configurationDoneRequest.
    response.body.supportsConfigurationDoneRequest = true;
    response.body.supportsFunctionBreakpoints = true;
    response.body.supportsEvaluateForHovers = false;
    response.body.supportsStepBack = false;
    response.body.supportsDelayedStackTraceLoading = true;
    response.body.supportsSetVariable = true;

    this.sendResponse(response);
  }

  protected configurationDoneRequest(
    response: DebugProtocol.ConfigurationDoneResponse, args: DebugProtocol.ConfigurationDoneArguments
  ): void {
    super.configurationDoneRequest(response, args);
  }

  protected attachRequest(response: DebugProtocol.AttachResponse, args: IAttachRequestArguments): void {

    if (!args.address || args.address === '') {
      this.sendErrorResponse(response, new Error('Must specify an address'));
      return;
    }

    if (!args.port || args.port <= 0 || args.port > 35535) {
      this.sendErrorResponse(response, new Error('Must specify a valid port'));
      return;
    }

    if (!args.localRoot || args.localRoot === '') {
      this.sendErrorResponse(response, new Error('Must specify a localRoot'));
      return;
    }

    this._attachArgs = args;
    if (args.debugLog in LOG_LEVEL) {
      this._debugLog = args.debugLog;
    } else {
      this.sendErrorResponse(response, new Error('No log level given'));
    }

    this.connectToDebugServer(response, args);
  }

  protected launchRequest(response: DebugProtocol.LaunchResponse, args: ILaunchRequestArguments) {

    if (!args.address || args.address === '') {
      this.sendErrorResponse(response, new Error('Must specify an address'));
      return;
    }
    if (!args.port || args.port <= 0 || args.port > 35535) {
      this.sendErrorResponse(response, new Error('Must specify a valid port'));
      return;
    }
    if (!args.localRoot || args.localRoot === '') {
      this.sendErrorResponse(response, new Error('Must specify a localRoot'));
      return;
    }

    this._launchArgs = args;
    if (args.debugLog in LOG_LEVEL) {
      this._debugLog = args.debugLog;
    } else {
      this.sendErrorResponse(response, new Error('No log level given'));
    }

    this.connectToDebugServer(response, args);
  }

  private connectToDebugServer(response: DebugProtocol.LaunchResponse | DebugProtocol.AttachResponse,
                               args: ILaunchRequestArguments | IAttachRequestArguments): void {
    const protocolDelegate = <EscargotDebugProtocolDelegate>{
      onBreakpointHit: (ref: EscargotMessageBreakpointHit, type: string) => this.onBreakpointHit(ref, type),
      onExceptionHit: (data: EscargotMessageExceptionHit) => this.onExceptionHit(data),
      onScriptParsed: (data: EscargotMessageScriptParsed) => this.onScriptParsed(data),
    };

    this._protocolhandler = new EscargotDebugProtocolHandler(
      protocolDelegate, (message: any, level: number = LOG_LEVEL.VERBOSE) => this.log(message, level)
    );
    this._debuggerClient = new EscargotDebuggerClient(<EscargotDebuggerOptions>{
      delegate: {
        onMessage: (message: Uint8Array) => this._protocolhandler.onMessage(message),
        onClose: () => this.onClose()
      },
      host: args.address,
      port: args.port
    });
    this._protocolhandler.debuggerClient = this._debuggerClient;

    this._debuggerClient.connect()
    .then(() => {
      this.log(`Connected to: ${args.address}:${args.port}`, LOG_LEVEL.SESSION);
      this.sendResponse(response);
    })
    .catch(error => {
      this.log(error.message, LOG_LEVEL.ERROR);
      this.sendErrorResponse(response, error);
    });
  }

  protected disconnectRequest(
    response: DebugProtocol.DisconnectResponse, args: DebugProtocol.DisconnectArguments
  ): void {
    this._debuggerClient.disconnect();
    this.sendEvent(new TerminatedEvent());
    this.sendResponse(response);
  }


  protected continueRequest(response: DebugProtocol.ContinueResponse, args: DebugProtocol.ContinueArguments): void {
    this._protocolhandler.resume()
      .then(() => {
        this.sendResponse(response);
      })
      .catch(error => this.sendErrorResponse(response, <Error>error));
  }

  protected nextRequest(response: DebugProtocol.NextResponse, args: DebugProtocol.NextArguments): void {
    this._protocolhandler.stepOver()
    .then(() => {
      this.sendResponse(response);
    })
    .catch(error => this.sendErrorResponse(response, <Error>error));
  }

  protected stepInRequest(response: DebugProtocol.StepInResponse, args: DebugProtocol.StepInArguments): void {
    this._protocolhandler.stepInto()
      .then(() => {
        this.sendResponse(response);
      })
      .catch(error => this.sendErrorResponse(response, <Error>error));
  }

  protected async setBreakPointsRequest(
    response: DebugProtocol.SetBreakpointsResponse, args: DebugProtocol.SetBreakpointsArguments
  ): Promise<void> {
    const filename: string = args.source.name;
    const vscodeBreakpoints: DebugProtocol.Breakpoint[] = args.breakpoints!.map(b => ({verified: false, line: b.line}));

    try {
      const scriptId: number = this._protocolhandler.getScriptIdByName(filename);
      const activeBps: Breakpoint[] = this._protocolhandler.getActiveBreakpointsByScriptId(scriptId);

      // Get the new breakpoints.
      const activeBpsLines: number[] = activeBps.map(b => b.line);
      const newBps: DebugProtocol.Breakpoint[] = vscodeBreakpoints.filter(b => activeBpsLines.indexOf(b.line) === -1);

      const newBreakpoints: TemporaryBreakpoint[] = await Promise.all(newBps.map(async (breakpoint, index) => {
        try {
          const jerryBreakpoint: Breakpoint = this._protocolhandler.findBreakpoint(scriptId, breakpoint.line);
          await this._protocolhandler.updateBreakpoint(jerryBreakpoint, true);
          return <TemporaryBreakpoint>{verified: true, line: breakpoint.line};
        } catch (error) {
          this.log(error.message, LOG_LEVEL.ERROR);
          return <TemporaryBreakpoint>{verified: false, line: breakpoint.line, message: (<Error>error).message};
        }
      }));

      // Get the persisted breakpoints.
      const newBreakpointsLines: number[] = newBreakpoints.map(b => b.line);
      const persistingBreakpoints: TemporaryBreakpoint[] = vscodeBreakpoints
                                    .filter(b => newBreakpointsLines.indexOf(b.line) === -1)
                                    .map(b => ({verified: true, line: b.line}));

      // Get the removable breakpoints.
      const vscodeBreakpointsLines: number[] = vscodeBreakpoints.map(b => b.line);
      const removeBps: Breakpoint[] = activeBps.filter(b => vscodeBreakpointsLines.indexOf(b.line) === -1);

      removeBps.forEach(async b => {
        const jerryBreakpoint = this._protocolhandler.findBreakpoint(scriptId, b.line);
        await this._protocolhandler.updateBreakpoint(jerryBreakpoint, false);
      });

      response.body = { breakpoints: [...persistingBreakpoints, ...newBreakpoints] };
    } catch (error) {
      this.log(error.message, LOG_LEVEL.ERROR);
      this.sendErrorResponse(response, <Error>error);
      return;
    }

    this.sendResponse(response);
  }

  protected async setFunctionBreakPointsRequest(
    response: DebugProtocol.SetFunctionBreakpointsResponse, args: DebugProtocol.SetFunctionBreakpointsArguments
  ): Promise<void> {
    const vscodeFunctionBreakpoints: DebugProtocol.FunctionBreakpoint[] = args.breakpoints;

    try {
      let persistingFBreakpoints: TemporaryBreakpoint[] = [];
      let newFBreakpoints: TemporaryBreakpoint[] = [];
      let undefinedFBreakpoins: TemporaryBreakpoint[] = [];

      await Promise.all(this._protocolhandler.getSources().map(async (src, id) => {
        const scriptId = id + 1;
        const inactiveFBps: Breakpoint[] = this._protocolhandler.getInactiveFunctionBreakpointsByScriptId(scriptId);
        const vscodeFunctionBreakpointNames: string[] = vscodeFunctionBreakpoints.map(b => b.name);

        const newFBs = inactiveFBps.filter(b => vscodeFunctionBreakpointNames.indexOf(b.func.name) !== -1);

        // Get the new breakpoints.
        newFBreakpoints = [
          ...newFBreakpoints,
          ...await Promise.all(newFBs.map(async (breakpoint) => {
            try {
              await this._protocolhandler.updateBreakpoint(breakpoint, true);
              return <TemporaryBreakpoint>{verified: true, line: breakpoint.line};
            } catch (error) {
              this.log(error.message, LOG_LEVEL.ERROR);
              return <TemporaryBreakpoint>{verified: false, line: breakpoint.line, message: (<Error>error).message};
            }
          }))
        ];

        // Get the persisted breakpoints.
        const possibleFBs = this._protocolhandler.getPossibleFunctionBreakpointsByScriptId(scriptId);
        persistingFBreakpoints = [
          ...persistingFBreakpoints,
          ...possibleFBs.filter(b => {
            return newFBs.map(b => b.func.name).indexOf(b.func.name) === -1 &&
                  vscodeFunctionBreakpointNames.indexOf(b.func.name) !== -1;
          }).map(b => <TemporaryBreakpoint>{verified: true, line: b.line})
        ];

        // Get the removable breakpoints.
        const activeFBs: Breakpoint[] = this._protocolhandler.getActiveFunctionBreakpointsByScriptId(scriptId);
        const removeBps: Breakpoint[] = activeFBs.filter(b => {
          return vscodeFunctionBreakpointNames.indexOf(b.func.name) === -1;
        });

        removeBps.forEach(async b => {
          const jerryBreakpoint = this._protocolhandler.findBreakpoint(scriptId, b.line);
          await this._protocolhandler.updateBreakpoint(jerryBreakpoint, false);
        });

        undefinedFBreakpoins = [
          ...undefinedFBreakpoins,
          ...vscodeFunctionBreakpoints.filter(b => {
            return possibleFBs.map(p => p.func.name).indexOf(b.name) === -1;
          }).map(b => <TemporaryBreakpoint>{verified: false, message: 'No function found'})
        ];
      }));

      response.body = { breakpoints: [...persistingFBreakpoints, ...newFBreakpoints, ...undefinedFBreakpoins] };
    } catch (error) {
      this.log(error, LOG_LEVEL.ERROR);
      this.sendErrorResponse(response, <Error>error);
      return;
    }

    this.sendResponse(response);
  }

  protected async stackTraceRequest(
    response: DebugProtocol.StackTraceResponse, args: DebugProtocol.StackTraceArguments
  ): Promise<void> {
    try {
      const currentArgs = this._attachArgs || this._launchArgs;
      const backtraceData: EscargotBacktraceResult = await this._protocolhandler.requestBacktrace(args.startFrame,
                                                                                               args.levels);
      const stk = backtraceData.backtrace.map((f, i) => new StackFrame(
        1000 + i,
        f.func.name || 'global',
        this.pathToSource(`${currentArgs.localRoot}/${this.pathToBasename(f.func.sourceName)}`),
        f.line,
        f.func.column)
      );

      response.body = {
        stackFrames: stk,
        totalFrames: backtraceData.totalFrames
      };

      this.sendResponse(response);
    } catch (error) {
      this.log(error.message, LOG_LEVEL.ERROR);
      this.sendErrorResponse(response, 0, (<Error>error).message);
    }
  }

  // Overrides.
  protected dispatchRequest(request: DebugProtocol.Request): void {
    const log = `-> ${request.command}Request\n${Util.inspect(request, { depth: Infinity })}\n`;
    this.log(log, LOG_LEVEL.SESSION);

    super.dispatchRequest(request);
  }

  public sendResponse(response: DebugProtocol.Response): void {
    const log = `<- ${response.command}Response\n${Util.inspect(response, { depth: Infinity })}\n`;
    this.log(log, LOG_LEVEL.SESSION);

    super.sendResponse(response);
  }

  public sendEvent(event: DebugProtocol.Event, bypassLog: boolean = false): void {
    if (!bypassLog) {
      const log = `<- ${event.event}Event\n${Util.inspect(event, { depth: Infinity })}\n`;
      this.log(log, LOG_LEVEL.SESSION);
    }

    super.sendEvent(event);
  }

  protected sendErrorResponse(
    response: DebugProtocol.Response,
    error: Error,
    dest?: ErrorDestination
  ): void;

  protected sendErrorResponse(
    response: DebugProtocol.Response,
    codeOrMessage: number | DebugProtocol.Message,
    format?: string,
    variables?: any,
    dest?: ErrorDestination
  ): void;

  protected sendErrorResponse(response: DebugProtocol.Response) {
    if (arguments[1] instanceof Error) {
      const error = arguments[1] as Error & {code?: number | string; errno?: number};
      const dest = arguments[2] as ErrorDestination;

      let code: number;

      if (typeof error.code === 'number') {
        code = error.code as number;
      } else if (typeof error.errno === 'number') {
        code = error.errno;
      } else {
        code = 0;
      }

      super.sendErrorResponse(response, code, error.message, dest);
    } else {
      super.sendErrorResponse(response, arguments[1], arguments[2], arguments[3], arguments[4]);
    }
  }

  // Helper functions for event handling

  private onBreakpointHit(breakpointRef: EscargotMessageBreakpointHit, stopType: string): void {
    this.log('onBreakpointHit', LOG_LEVEL.SESSION);

    this.sendEvent(new StoppedEvent(stopType, EscargotDebugSession.THREAD_ID));
  }

  private onExceptionHit(data: EscargotMessageExceptionHit): void {
    this.log('onExceptionHit', LOG_LEVEL.SESSION);

    this.sendEvent(new StoppedEvent('exception', EscargotDebugSession.THREAD_ID, data.message));
  }

  private onScriptParsed(data: EscargotMessageScriptParsed): void {
    this.log('onScriptParsed', LOG_LEVEL.SESSION);

    this.handleSource(data);
  }

  private onClose(): void {
    this.log('onClose', LOG_LEVEL.SESSION);

    this.sendEvent(new TerminatedEvent());
  }

  // General helper functions

  private handleSource(data: EscargotMessageScriptParsed): void {
    const src = this._protocolhandler.getSource(data.id);
    const currentArgs = this._attachArgs || this._launchArgs;
    if (src !== '') {
      const path = Path.join(`${currentArgs.localRoot}`, `${this.pathToBasename(data.name)}`);
      const write = c => Fs.writeSync(Fs.openSync(path, 'w'), c);

      if (Fs.existsSync(path)) {
        const content = Fs.readFileSync(path, {
          encoding: 'utf8',
          flag: 'r'
        });

        if (content !== src) {
          write(src);
        }
      } else {
        write(src);
      }
      this.sendEvent(new InitializedEvent());
    }
  }

  private pathToSource(path): Source {
    return new Source(this.pathToBasename(path), path);
  }

  private pathToBasename(path: string): string {
    if (path === '' || path === undefined) path = 'debug_eval.js';
    return Path.basename(path);
  }

  private log(message: any, level: number = LOG_LEVEL.VERBOSE): void {
    if (level === this._debugLog || this._debugLog === LOG_LEVEL.VERBOSE) {
      switch (typeof message) {
        case 'object':
          message = Util.inspect(message, { depth: Infinity });
          break;
        default:
          message = message.toString();
          break;
      }

      this.sendEvent(new OutputEvent(`[${LOG_LEVEL[level]}] ${message}\n`, 'console'), true);
    }
  }
}

DebugSession.run(EscargotDebugSession);