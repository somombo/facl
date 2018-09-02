
import { Request } from 'express'
import * as pathToRegex from 'path-to-regexp'
import { validVariableName, toUniformCase, WRITE_METHODS, READ_METHODS } from '../utils';

export type Condition = (ctx: any) => boolean
export type Action = string
export type Children = (Match | Allow)[]

export enum TokenClass {
  OPERATOR = "OPERATOR",
  LITERAL = "LITERAL",
  ITERABLE = "ITERABLE",
  IDENTIFIER = "IDENTIFIER",
  SERVICE = "SERVICE",
  CHILD = "CHILD"
}


/////////////////////////////////


export class Service {
  private _matches = []
  private _acl: ACL = []

  get acl(): ACL{ return this._acl } 
  get matches() { return this._matches }

  constructor(
    private type: string = 'cloudfunctions.https',
    matches: Match[] = [],
  ) {
    this.initRules(matches)
    this._matches = matches
  }

  private initRules(matches: Match[], currentAbsPath: string = ''){


    for (const match of matches) {

      const absolutePath = (currentAbsPath + match.relativeRoute)
                            .replace(' ', '')
                            .replace('//', '/')
                                
      let isMatchAny: boolean

      const absRoute: string = absolutePath.split('/')
        .map(token => {
          
          // it is a regular segment
          if ( !token.includes('{') ) return token

          const potentialVarName = token
            .replace(' ', '')
            .replace('{', '')
            .replace('}', '')
            .trim()

          const matchAnyTokens = potentialVarName.split('=')

          // if it a valid variablename
          if ( validVariableName.test( potentialVarName ) )  {
            return `:${potentialVarName}`
          }  

          // if it is a valid matchAny
          if(
            matchAnyTokens.length === 2 
              && validVariableName.test( matchAnyTokens[0] )
              && matchAnyTokens[1] === '**'
          ){
            isMatchAny = true
            return null
          }  

          throw 'Malformed Route segment: ' + token
          

        })
        .filter( t => t !== null) // removes any token that was previously determined to be a matchAny
        .join('/')



      this._acl.push(
        new Rule(absRoute, match.allows, isMatchAny)
      )  
      
      this.initRules(match.subMatches, absolutePath)
    }
  }  
}


export class Match {
  constructor(
    public relativeRoute: string, 
    public allows: Allow[] = [], 
    public subMatches: Match[] = []
  ){ }
  // absolutePathTokens: string[];
}

export class Allow {
  private _actions: Action[]

  set actions(val: Action[]) {
    
    this._actions = val.map(toUniformCase)
  }

  get actions() {
    
    return this._actions
  }

  get methods(): Set<Action> {
    function actionToMethods(axn: Action): Action[] {
      if (toUniformCase(axn).trim() === 'write'){
        return WRITE_METHODS
      } else 
      
      if (toUniformCase(axn).trim() === 'read'){
        return READ_METHODS
      }
      return [axn]
    }

    return new Set<Action>(
      this.actions
      .map(actionToMethods)
      .reduce((a, b) => a.concat(b), [])
    )
  }

  constructor(
    actions: Action[], 
    private condition: Condition = _ => false
  ) {
    this.actions = actions
  }

  isAllowedAction(action: string): boolean {

    return this.methods.has(toUniformCase(action).trim() as Action)
  }

  isAllowedReqIn(context: any = {}): boolean {
    const result =  this.condition(context)
         
    return result 
  }
}


///////////////////////////////

export function service(type: string = 'https', ...matches: Match[]) {
  return new Service(type, matches || [])
}

export function match(relativeRoute: string, ...children: Children){
  
  return new Match(
    relativeRoute, 
    ((children || []) as Allow[]).filter(c => c.constructor.name === Allow.name), 
    ((children || []) as Match[]).filter(c => c.constructor.name === Match.name),   
  )
}

export function allow(actions: string, condition: Condition = _ => false){

  const actionsList: Action[] = actions
    .split(',')
    .map(a => a.trim())
    .map(toUniformCase)
    .filter(a => !!a)

  return new Allow(actionsList, condition)
}


// export interface Rule {
//   path: string
//   matchAny?: boolean
//   allows?: Allow[]
// }
export type ACL = Rule[]
export class Rule {

  constructor(
    private _absolutePath: string, 
    private _allows: Allow[] = [], 
    private _matchAny?: boolean 
  ){  }
  
  isAccessibleResource(inputPath: string): boolean {
    return pathToRegex(this.absolutePath, null, { end: !this.matchAny }).test(inputPath) 
  }
  
  get absolutePath(){ return this._absolutePath }
  get allows(){ return this._allows }
  get matchAny(){ return this._matchAny }
}

// TODO: currenly mock, create parser
// takes in string source code representing the rules
// returns AST or similar data structure respresenting the syntactic analysis
export function compile(source: string | Service): ACL {
  if (typeof source === 'string' || source instanceof String){
    throw new Error('Does not yet support actual DSL sourcecode. \nPlease provide Service object instead')
  }

  return (source as Service).acl
}
