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

// Expected JerryScript debugger protocol version.
export const ESCARGOT_DEBUGGER_VERSION = 9;

// Packages sent from the server to the client.
export enum SERVER {
  ESCARGOT_DEBUGGER_VERSION = 0,
  ESCARGOT_DEBUGGER_CONFIGURATION = 1,
  ESCARGOT_DEBUGGER_CLOSE_CONNECTION = 2,
  ESCARGOT_DEBUGGER_RELEASE_FUNCTION = 3,
  ESCARGOT_DEBUGGER_PARSE_NODE = 4,
  ESCARGOT_DEBUGGER_PARSE_ERROR = 5,
  // These four must be in the same order.
  ESCARGOT_DEBUGGER_SOURCE_8BIT = 6,
  ESCARGOT_DEBUGGER_SOURCE_8BIT_END = 7,
  ESCARGOT_DEBUGGER_SOURCE_16BIT = 8,
  ESCARGOT_DEBUGGER_SOURCE_16BIT_END = 9,
  // These four must be in the same order.
  ESCARGOT_DEBUGGER_FILE_NAME_8BIT = 10,
  ESCARGOT_DEBUGGER_FILE_NAME_8BIT_END = 11,
  ESCARGOT_DEBUGGER_FILE_NAME_16BIT = 12,
  ESCARGOT_DEBUGGER_FILE_NAME_16BIT_END = 13,
  // These four must be in the same order.
  ESCARGOT_DEBUGGER_FUNCTION_NAME_8BIT = 14,
  ESCARGOT_DEBUGGER_FUNCTION_NAME_8BIT_END = 15,
  ESCARGOT_DEBUGGER_FUNCTION_NAME_16BIT = 16,
  ESCARGOT_DEBUGGER_FUNCTION_NAME_16BIT_END = 17,
  ESCARGOT_DEBUGGER_BREAKPOINT_LOCATION = 18,
  ESCARGOT_DEBUGGER_FUNCTION_PTR = 19,
  ESCARGOT_DEBUGGER_BREAKPOINT_HIT = 20,
  ESCARGOT_DEBUGGER_EXCEPTION_HIT = 21,
  ESCARGOT_DEBUGGER_BACKTRACE_TOTAL = 22,
  // These four must be in the same order.
  ESCARGOT_DEBUGGER_BACKTRACE_8BIT = 23,
  ESCARGOT_DEBUGGER_BACKTRACE_8BIT_END = 24,
  ESCARGOT_DEBUGGER_BACKTRACE_16BIT = 25,
  ESCARGOT_DEBUGGER_BACKTRACE_16BIT_END = 26,
}

// Packages sent from the client to the server.
export enum CLIENT {
  ESCARGOT_DEBUGGER_FUNCTION_RELEASED = 0,
  ESCARGOT_DEBUGGER_UPDATE_BREAKPOINT = 1,
  ESCARGOT_DEBUGGER_CONTINUE = 2,
  ESCARGOT_DEBUGGER_STEP = 3,
  ESCARGOT_DEBUGGER_NEXT = 4,
  ESCARGOT_DEBUGGER_GET_BACKTRACE = 5,
}