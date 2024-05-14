/*---------------------------------------------------------
 * Copyright (C) Microsoft Corporation. All rights reserved.
 *--------------------------------------------------------*/

import { EventEmitter } from 'events';
import { ShakespearianDat } from './splDAT'

export interface FileAccessor {
	isWindows: boolean;
	readFile(path: string): Promise<Uint8Array>;
	writeFile(path: string, contents: Uint8Array): Promise<void>;
}

export interface IRuntimeBreakpoint {
	id: number;
	line: number;
	verified: boolean;
}

interface IRuntimeStepInTargets {
	id: number;
	label: string;
}

interface IRuntimeStackFrame {
	index: number;
	name: string;
	file: string;
	line: number;
	column?: number;
	instruction?: number;
}

interface IRuntimeStack {
	count: number;
	frames: IRuntimeStackFrame[];
}

interface RuntimeDisassembledInstruction {
	address: number;
	instruction: string;
	line?: number;
}

export type IRuntimeVariableType = number | boolean | string | RuntimeVariable[];

export class RuntimeVariable {
	private _memory?: Uint8Array;

	public reference?: number;

	public get value() {
		return this._value;
	}

	public set value(value: IRuntimeVariableType) {
		this._value = value;
		this._memory = undefined;
	}

	public get memory() {
		if (this._memory === undefined && typeof this._value === 'string') {
			this._memory = new TextEncoder().encode(this._value);
		}
		return this._memory;
	}

	constructor(public readonly name: string, private _value: IRuntimeVariableType) {}

	public setMemory(data: Uint8Array, offset = 0) {
		const memory = this.memory;
		if (!memory) {
			return;
		}

		memory.set(data, offset);
		this._memory = memory;
		this._value = new TextDecoder().decode(memory);
	}
}

interface Word {
	name: string;
	line: number;
	index: number;
}

export function timeout(ms: number) {
	return new Promise(resolve => setTimeout(resolve, ms));
}

function romanToInt(s: string): number {
    const romanValues: { [key: string]: number } = { I: 1, V: 5, X: 10, L: 50, C: 100, D: 500, M: 1000 }; 
    let result: number = 0;
    for (let i: number = 0; i < s.length; i++) {
        if (romanValues[s[i]] < romanValues[s[i + 1]]) {
            result -= romanValues[s[i]]; 
        } else {
            result += romanValues[s[i]];
        }
    }
    return result;
}

function findNext(l: string) {
    var out = -1;
    const attempt = (char: string) => {
        var pos = l.indexOf(char);
        if (pos != -1 && (out > pos || out == -1)) {
            out = pos;
        }
    }
    attempt('.');
    attempt('!');
    return out + 1;
}

/**
 * A SPL runtime with minimal debugger functionality.
 * SPLRuntime is a hypothetical (aka "SPL") "execution engine with debugging support":
 * it takes a spl (*.md) file and "executes" it by "running" through the text lines
 * and searching for "command" patterns that trigger some debugger related functionality (e.g. exceptions).
 * When it finds a command it typically emits an event.
 * The runtime can not only run through the whole file but also executes one line at a time
 * and stops on lines for which a breakpoint has been registered. This functionality is the
 * core of the "debugging support".
 * Since the SPLRuntime is completely independent from VS Code or the Debug Adapter Protocol,
 * it can be viewed as a simplified representation of a real "execution engine" (e.g. node.js)
 * or debugger (e.g. gdb).
 * When implementing your own debugger extension for VS Code, you probably don't need this
 * class because you can rely on some existing debugger or runtime.
 */
export class SPLRuntime extends EventEmitter {

	// the initial (and one and only) file we are 'debugging'
	private _sourceFile: string = '';
	public get sourceFile() {
		return this._sourceFile;
	}

	private variables = new Map<string, RuntimeVariable>();

	// the contents (= lines) of the one and only file
	private sourceLines: string[] = [];
    private sourceAll: string = '';
	private instructions: Word[] = [];
	private starts: number[] = [];
	private ends: number[] = [];

	// This is the next line that will be 'executed'
	private _currentLine = 0;
	private get currentLine() {
		return this._currentLine;
	}
	private set currentLine(x) {
		this._currentLine = x;
		this.instruction = this.starts[x];
	}
	private currentColumn: number | undefined;

	// This is the next instruction that will be 'executed'
	public instruction = 0;

    // When you hit a breakpoint, then this causes the program to end when you try to continue.
    private errored = new RuntimeVariable('errored', false);

    // This is the info about what's going on with the program, for the stack trace.
    private info = new Map<string, RuntimeVariable>();

    // These are all the acts and scenes initialised
    private acts = new Map<number, RuntimeVariable>();
    private scenes = new Map<number, RuntimeVariable>();

	// maps from sourceFile to array of IRuntimeBreakpoint
	private breakPoints = new Map<string, IRuntimeBreakpoint[]>();

	// all instruction breakpoint addresses
	private instructionBreakpoints = new Set<number>();

	// since we want to send breakpoint events, we will assign an id to every event
	// so that the frontend can match events with breakpoints.
	private breakpointId = 1;

	private breakAddresses = new Map<string, string>();

	private namedException: string | undefined;
	private otherExceptions = false;


	constructor(private fileAccessor: FileAccessor) {
		super();     
	}

	/**
	 * Start executing the given program.
	 */
	public async start(program: string, debug: boolean): Promise<void> {

		await this.loadSource(this.normalizePathAndCasing(program));

        this.info.set('init', new RuntimeVariable('init', false))
        this.info.set('act', new RuntimeVariable('act', 0))
        this.info.set('scene', new RuntimeVariable('act', 0))

		if (debug) {
			await this.verifyBreakpoints(this._sourceFile);

			// we just start to run until we hit a breakpoint, an exception, or the end of the program
			this.continue(false);
		} else {
			this.continue(false);
		}
	}

	/**
	 * Continue execution to the end/beginning.
	 */
	public continue(reverse: boolean) {

		while (!this.executeLine(this.currentLine, reverse)) {
			if (this.updateCurrentLine(reverse)) {
				break;
			}
			if (this.findNextStatement(reverse)) {
				break;
			}
		}
	}

	/**
	 * Step to the next/previous non empty line.
	 */
	public step(instruction: boolean, reverse: boolean) {

		if (instruction) {
			if (reverse) {
				this.instruction--;
			} else {
				this.instruction++;
			}
			this.sendEvent('stopOnStep');
		} else {
			if (!this.executeLine(this.currentLine, reverse)) {
				if (!this.updateCurrentLine(reverse)) {
					this.findNextStatement(reverse, 'stopOnStep');
				}
			}
		}
	}

	private updateCurrentLine(reverse: boolean): boolean {
		if (reverse) {
			if (this.currentLine > 0) {
				this.currentLine--;
			} else {
				// no more lines: stop at first line
				this.currentLine = 0;
				this.currentColumn = undefined;
				return true;
			}
		} else {
			if (this.currentLine < this.sourceLines.length-1) {
				this.currentLine++;
			} else {
				// no more lines: run to end
				this.currentColumn = undefined;
				this.sendEvent('end');
				return true;
			}
		}
		return false;
	}

	/**
	 * "Step into" for SPL debug means: go to next character
	 */
	public stepIn(targetId: number | undefined) {
		if (typeof targetId === 'number') {
			this.currentColumn = targetId;
			this.sendEvent('stopOnStep');
		} else {
			if (typeof this.currentColumn === 'number') {
				if (this.currentColumn <= this.sourceLines[this.currentLine].length) {
					this.currentColumn += 1;
				}
			} else {
				this.currentColumn = 1;
			}
			this.sendEvent('stopOnStep');
		}
	}

	/**
	 * "Step out" for SPL debug means: go to previous character
	 */
	public stepOut() {
		if (typeof this.currentColumn === 'number') {
			this.currentColumn -= 1;
			if (this.currentColumn === 0) {
				this.currentColumn = undefined;
			}
		}
		this.sendEvent('stopOnStep');
	}

	public getStepInTargets(frameId: number): IRuntimeStepInTargets[] {

		const line = this.getLine();
		const words = this.getWords(this.currentLine, line);

		// return nothing if frameId is out of range
		if (frameId < 0 || frameId >= words.length) {
			return [];
		}

		const { name, index  }  = words[frameId];

		// make every character of the frame a potential "step in" target
		return name.split('').map((c, ix) => {
			return {
				id: index + ix,
				label: `target: ${c}`
			};
		});
	}

	/**
	 * Returns a fake 'stacktrace' where every 'stackframe' is a word from the current line.
	 */
	public stack(startFrame: number, endFrame: number): IRuntimeStack {
        // parsing stack: character, line, event, scene, act, play
		const line = this.getLine();
		const words = this.getWords(this.currentLine, line);
		words.push({ name: 'BOTTOM', line: -1, index: -1 });	// add a sentinel so that the stack is never empty...

		// if the line contains the word 'disassembly' we support to "disassemble" the line by adding an 'instruction' property to the stackframe
		const instruction = line.indexOf('disassembly') >= 0 ? this.instruction : undefined;

		const column = typeof this.currentColumn === 'number' ? this.currentColumn : undefined;

		const frames: IRuntimeStackFrame[] = [];
		// every word of the current line becomes a stack frame.
		for (let i = startFrame; i < Math.min(endFrame, words.length); i++) {

			const stackFrame: IRuntimeStackFrame = {
				index: i,
				name: `${words[i].name}(${i})`,	// use a word of the line as the stackframe name
				file: this._sourceFile,
				line: this.currentLine,
				column: column, // words[i].index
				instruction: instruction ? instruction + i : 0
			};

			frames.push(stackFrame);
		}

		return {
			frames: frames,
			count: words.length
		};
	}

	/*
	 * Determine possible column breakpoint positions for the given line.
	 * Here we return the start location of words with more than 8 characters.
	 */
	public getBreakpoints(path: string, line: number): number[] {
		return this.getWords(line, this.getLine(line)).filter(w => w.name.length > 8).map(w => w.index);
	}

	/*
	 * Set breakpoint in file with given line.
	 */
	public async setBreakPoint(path: string, line: number): Promise<IRuntimeBreakpoint> {
		path = this.normalizePathAndCasing(path);

		const bp: IRuntimeBreakpoint = { verified: false, line, id: this.breakpointId++ };
		let bps = this.breakPoints.get(path);
		if (!bps) {
			bps = new Array<IRuntimeBreakpoint>();
			this.breakPoints.set(path, bps);
		}
		bps.push(bp);

		await this.verifyBreakpoints(path);

		return bp;
	}

	/*
	 * Clear breakpoint in file with given line.
	 */
	public clearBreakPoint(path: string, line: number): IRuntimeBreakpoint | undefined {
		const bps = this.breakPoints.get(this.normalizePathAndCasing(path));
		if (bps) {
			const index = bps.findIndex(bp => bp.line === line);
			if (index >= 0) {
				const bp = bps[index];
				bps.splice(index, 1);
				return bp;
			}
		}
		return undefined;
	}

	public clearBreakpoints(path: string): void {
		this.breakPoints.delete(this.normalizePathAndCasing(path));
	}

	public setDataBreakpoint(address: string, accessType: 'read' | 'write' | 'readWrite'): boolean {

		const x = accessType === 'readWrite' ? 'read write' : accessType;

		const t = this.breakAddresses.get(address);
		if (t) {
			if (t !== x) {
				this.breakAddresses.set(address, 'read write');
			}
		} else {
			this.breakAddresses.set(address, x);
		}
		return true;
	}

	public clearAllDataBreakpoints(): void {
		this.breakAddresses.clear();
	}

	public setExceptionsFilters(namedException: string | undefined, otherExceptions: boolean): void {
		this.namedException = namedException;
		this.otherExceptions = otherExceptions;
	}

	public setInstructionBreakpoint(address: number): boolean {
		this.instructionBreakpoints.add(address);
		return true;
	}

	public clearInstructionBreakpoints(): void {
		this.instructionBreakpoints.clear();
	}

	public async getGlobalVariables(cancellationToken?: () => boolean ): Promise<RuntimeVariable[]> {

		let a: RuntimeVariable[] = [];

		for (let i = 0; i < 10; i++) {
			a.push(new RuntimeVariable(`global_${i}`, i));
			if (cancellationToken && cancellationToken()) {
				break;
			}
			await timeout(1000);
		}

		return a;
	}

	public getLocalVariables(): RuntimeVariable[] {
		return Array.from(this.variables, ([name, value]) => value);
	}

	public getLocalVariable(name: string): RuntimeVariable | undefined {
		return this.variables.get(name);
	}

	/**
	 * Return words of the given address range as "instructions"
	 */
	public disassemble(address: number, instructionCount: number): RuntimeDisassembledInstruction[] {

		const instructions: RuntimeDisassembledInstruction[] = [];

		for (let a = address; a < address + instructionCount; a++) {
			if (a >= 0 && a < this.instructions.length) {
				instructions.push({
					address: a,
					instruction: this.instructions[a].name,
					line: this.instructions[a].line
				});
			} else {
				instructions.push({
					address: a,
					instruction: 'nop'
				});
			}
		}

		return instructions;
	}

	// private methods

	private getLine(line?: number): string {
		return this.sourceLines[line === undefined ? this.currentLine : line];
	}

	private getWords(l: number, line: string): Word[] {
		// break line into words
		const WORD_REGEXP = /[a-z]+/ig;
		const words: Word[] = [];
		let match: RegExpExecArray | null;
		while (match = WORD_REGEXP.exec(line)) {
			words.push({ name: match[0], line: l, index: match.index });
		}
		return words;
	}

	private async loadSource(file: string): Promise<void> {
		if (this._sourceFile !== file) {
			this._sourceFile = this.normalizePathAndCasing(file);
			this.initializeContents(await this.fileAccessor.readFile(file));
		}
	}

	private initializeContents(memory: Uint8Array) {
        this.sourceAll = new TextDecoder().decode(memory)
		this.sourceLines = this.sourceAll.split(/\r?\n/);

		this.instructions = [];

		this.starts = [];
		this.instructions = [];
		this.ends = [];

		for (let l = 0; l < this.sourceLines.length; l++) {
			this.starts.push(this.instructions.length);
			const words = this.getWords(l, this.sourceLines[l]);
			for (let word of words) {
				this.instructions.push(word);
			}
			this.ends.push(this.instructions.length);
		}
	}

	/**
	 * return true on stop
	 */
	 private findNextStatement(reverse: boolean, stepEvent?: string): boolean {

		for (let ln = this.currentLine; reverse ? ln >= 0 : ln < this.sourceLines.length; reverse ? ln-- : ln++) {

			// is there a source breakpoint?
			const breakpoints = this.breakPoints.get(this._sourceFile);
			if (breakpoints) {
				const bps = breakpoints.filter(bp => bp.line === ln);
				if (bps.length > 0) {

					// send 'stopped' event
					this.sendEvent('stopOnBreakpoint');

					// the following shows the use of 'breakpoint' events to update properties of a breakpoint in the UI
					// if breakpoint is not yet verified, verify it now and send a 'breakpoint' update event
					if (!bps[0].verified) {
						bps[0].verified = true;
						this.sendEvent('breakpointValidated', bps[0]);
					}

					this.currentLine = ln;
					return true;
				}
			}

			const line = this.getLine(ln);
			if (line.length > 0) {
				this.currentLine = ln;
				break;
			}
		}
		if (stepEvent) {
			this.sendEvent(stepEvent);
			return true;
		}
		return false;
	}

	/**
	 * "execute a line" of the readme spl.
	 * Returns true if execution sent out a stopped event and needs to stop.
	 */
	private executeLine(ln: number, reverse: boolean): boolean {
        if (this.errored.value) {
            this.sendEvent('end');
            return true;
        }
		// first "execute" the instructions associated with this line and potentially hit instruction breakpoints
		while (reverse ? this.instruction >= this.starts[ln] : this.instruction < this.ends[ln]) {
			reverse ? this.instruction-- : this.instruction++;
			if (this.instructionBreakpoints.has(this.instruction)) {
				this.sendEvent('stopOnInstructionBreakpoint');
				return true;
			}
		}

		var line = this.getLine(ln);
        var offset = 0;
        var res;
        while (line.trimStart().length != 0) {
            res = this.executeLinePart(ln, line, offset);
            if (typeof res == 'boolean') {
                return res;
            }
            offset += res;
            line = line.slice(offset);
            if (line.trimStart().length != 0) {
                this.sendEvent('output', 'warning', 'Multiple statements on one line', this._sourceFile, ln, offset + (line.length - line.trimStart().length));
            }
        }
        return false;
    }
    private executeLinePart(ln: number, line: string, charOffset: number): number | boolean {
        const tl = line.trim()
        const tldiff = charOffset + (line.length - line.trimStart().length)

        if (tl.length == 0) {
            return false;
        }

        if (!this.info.get('init')?.value) {
            if (line.includes(".")) {
                this.info.set('init', new RuntimeVariable('init', true));
                return findNext(line);
            } else {
                return false;
            }
        }

        if (line.trimStart().toLowerCase().startsWith('act ')) {
            var act = tl.slice(4, tl.indexOf(','));
            var spacingdiff = (act.length - act.trimStart().length) + 4;
            act = act.trimStart()
            if (act.indexOf(':') == -1) {
                this.error("Expecting ':'", ln,  tldiff);
                return true;
            }
            act = act.slice(0, act.indexOf(':')).trimEnd();
            var actNum = romanToInt(act);
            if (Number.isNaN(actNum)) {
                this.error('Act number not a roman numeral!', ln,  tldiff + spacingdiff);
                return true;
            }
            var currentAct = this.info.get('act')?.value;
            if (typeof currentAct != 'number') {
                this.error('Unknown error: act is not a number?!?!?', ln,  tldiff + spacingdiff); // This should never occur, is just to appease the linter
                return true;
            }
            if (actNum != currentAct + 1) {
                this.sendEvent('output', 'warning', 
                               `Act ${act} does not follow logical progression! It's value is ${actNum.toString()} wheras the next act number expected is ${currentAct + 1}!`, 
                               this._sourceFile, ln, tldiff + spacingdiff);
            }
            let reg0 = new RegExp(`act +?${act} *?:`, "gi");
            var matches;
            var i = 0;
            while (matches = reg0.exec(this.sourceAll)) {
                // matches[1] will be each successive block of text between the pre tags
                console.log(matches[0]);
                i += 1;
            }
            if (i == 0) {
                this.error('Unknown error: no acts found?!?!?', ln,  tldiff + spacingdiff);
                return true;
            }
            if (i > 1) {
                this.error('Act numeral ' + act + ' is not unique! Used ' + i.toString() + ' times.', ln,  tldiff + spacingdiff);
                return true;
            }
            if (this.sourceAll.toLowerCase())
            this.info.set('act', new RuntimeVariable('act', actNum));
            this.info.set('scene', new RuntimeVariable('scene', 0));
            return findNext(line);
        }

        if (line.trimStart().toLowerCase().startsWith('scene ')) {
            var scene = tl.slice(6, tl.indexOf(',')).trimStart();
            var spacingdiff = (scene.length - scene.trimStart().length) + 6;
            if (scene.indexOf(':') == -1) {
                this.error("Expecting ':'", ln,  tldiff);
                return true;
            }
            scene = scene.slice(0, scene.indexOf(':')).trimEnd();
            var sceneNum = romanToInt(scene);
            if (Number.isNaN(sceneNum)) {
                this.error('Scene number not a roman numeral!', ln,  tldiff + spacingdiff);
                return true;
            }
            var currentScene = this.info.get('scene')?.value;
            if (typeof currentScene != 'number') {
                this.error('Unknown error: scene is not a number?!?!?', ln,  tldiff + spacingdiff); // This should never occur, is just to appease the linter
                return true;
            }
            if (sceneNum != currentScene + 1) {
                this.sendEvent('output', 'warning', 
                               `Scene ${scene} does not follow logical progression! It's value is ${sceneNum.toString()} wheras the next scene number expected is ${currentScene + 1}!`, 
                               this._sourceFile, ln, tldiff + spacingdiff);
            }
            let reg0 = new RegExp(`scene +?${scene} *?:`, "gi");
            var matches;
            var i = 0;
            var lineCharNums = this.sourceLines.slice(0, ln).map(function(str) {return str.length});
            var lineCharNum = lineCharNums.reduce((sum, current) => sum + current, 0);
            var from = this.sourceAll.toLowerCase().slice(0, lineCharNum).lastIndexOf('act');
            var to = this.sourceAll.toLowerCase().slice(lineCharNum + 3).indexOf('act') + lineCharNum + 3;
            if (to == -1) {
                to = this.sourceAll.length
            }
            while (matches = reg0.exec(this.sourceAll.slice(from, to))) {
                i += 1;
            }
            if (i == 0) {
                this.error('Unknown error: no scenes found?!?!?', ln,  tldiff + spacingdiff);
                return true;
            }
            if (i > 1) {
                this.error('Scene numeral ' + scene + ' is not unique! Used ' + i.toString() + ' times.', ln,  tldiff + spacingdiff);
                return true;
            }
            this.info.set('scene', new RuntimeVariable('scene', sceneNum));
            this.sendEvent('output', 'log', 'Act ' + this.info.get('act')?.value + ', Scene ' + this.info.get('scene')?.value, this._sourceFile, ln,  tldiff);
            return findNext(line);
        }

        if (this.info.get('act')?.value == 0) {
            if (tl.indexOf(',') == -1) {
                this.error("Expecting ','", ln, tldiff);
                return true;
            }
            var character = tl.slice(0, tl.indexOf(','));
            if (!ShakespearianDat.Characters.includes(character)) {
                this.error('Character name not valid!', ln, tldiff)
            }
            this.variables.set(character, new RuntimeVariable(character + ' info', [new RuntimeVariable('init', 'null')]))
            // this.sendEvent('output', 'log', 'character ' + character + ' found', this._sourceFile, ln,  tldiff);
            return findNext(line);
        }

        if (this.info.get('scene')?.value == 0) {
            this.error("Scene expected", ln, 0);
            return true;
        }

		// find variable accesses
		let reg0 = /\$([a-z][a-z0-9]*)(=(false|true|[0-9]+(\.[0-9]+)?|\".*\"|\{.*\}))?/ig;
		let matches0: RegExpExecArray | null;
		while (matches0 = reg0.exec(line)) {
			if (matches0.length === 5) {

				let access: string | undefined;

				const name = matches0[1];
				const value = matches0[3];

				let v = new RuntimeVariable(name, value);

				if (value && value.length > 0) {

					if (value === 'true') {
						v.value = true;
					} else if (value === 'false') {
						v.value = false;
					} else if (value[0] === '"') {
						v.value = value.slice(1, -1);
					} else if (value[0] === '{') {
						v.value = [
							new RuntimeVariable('fBool', true),
							new RuntimeVariable('fInteger', 123),
							new RuntimeVariable('fString', 'hello'),
							new RuntimeVariable('flazyInteger', 321)
						];
					} else {
						v.value = parseFloat(value);
					}

					if (this.variables.has(name)) {
						// the first write access to a variable is the "declaration" and not a "write access"
						access = 'write';
					}
					this.variables.set(name, v);
				} else {
					if (this.variables.has(name)) {
						// variable must exist in order to trigger a read access
						access = 'read';
					}
				}

				const accessType = this.breakAddresses.get(name);
				if (access && accessType && accessType.indexOf(access) >= 0) {
					this.sendEvent('stopOnDataBreakpoint', access);
					return true;
				}
			}
		}

		// if 'log(...)' found in source -> send argument to debug console
		const reg1 = /(log|prio|out|err)\(([^\)]*)\)/g;
		let matches1: RegExpExecArray | null;
		while (matches1 = reg1.exec(line)) {
			if (matches1.length === 3) {
				this.sendEvent('output', matches1[1], matches1[2], this._sourceFile, ln, matches1.index);
			}
		}

		// if pattern 'exception(...)' found in source -> throw named exception
		const matches2 = /exception\((.*)\)/.exec(line);
		if (matches2 && matches2.length === 2) {
			const exception = matches2[1].trim();
			if (this.namedException === exception) {
				this.sendEvent('stopOnException', exception);
				return true;
			} else {
				if (this.otherExceptions) {
					this.sendEvent('stopOnException', undefined);
					return true;
				}
			}
		} else {
			// if word 'exception' found in source -> throw exception
			if (line.indexOf('exception') >= 0) {
				if (this.otherExceptions) {
					this.sendEvent('stopOnException', undefined);
					return true;
				}
			}
		}

		// nothing interesting found -> continue
		return false;
	}

    private error(message: string, ln: number, charnum: number) {
        this.sendEvent('output', 'err', message, this._sourceFile, ln,charnum);
        this.sendEvent('stopOnException', message);
        this.errored = new RuntimeVariable('errored', true);
    }

	private async verifyBreakpoints(path: string): Promise<void> {

		const bps = this.breakPoints.get(path);
		if (bps) {
			await this.loadSource(path);
			bps.forEach(bp => {
				if (!bp.verified && bp.line < this.sourceLines.length) {
					const srcLine = this.getLine(bp.line);

					// if a line is empty or starts with '+' we don't allow to set a breakpoint but move the breakpoint down
					if (srcLine.length === 0 || srcLine.indexOf('+') === 0) {
						bp.line++;
					}
					// if a line starts with '-' we don't allow to set a breakpoint but move the breakpoint up
					if (srcLine.indexOf('-') === 0) {
						bp.line--;
					}
					// don't set 'verified' to true if the line contains the word 'lazy'
					// in this case the breakpoint will be verified 'lazy' after hitting it once.
					if (srcLine.indexOf('lazy') < 0) {
						bp.verified = true;
						this.sendEvent('breakpointValidated', bp);
					}
				}
			});
		}
	}

	private sendEvent(event: string, ... args: any[]): void {
		setTimeout(() => {
			this.emit(event, ...args);
		}, 0);
	}

	private normalizePathAndCasing(path: string) {
		if (this.fileAccessor.isWindows) {
			return path.replace(/\//g, '\\').toLowerCase();
		} else {
			return path.replace(/\\/g, '/');
		}
	}
}
