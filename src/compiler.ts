import { ACL, Service,  Match, Allow, Children} from "./parser/ast";
import { service, match, allow } from "./parser/ast";
import './parser' 

import {join} from 'path'


import { writeFileSync } from "fs";
import op from './parser/operators'

import { TokenClass } from './parser/ast'


// const parser = require('./parser/index.js')
import * as parser from './parser/index'

// type AST = any
interface AST {
  class:TokenClass
  [key: string]: any;

}

function parse(rules_source: string): AST {

  const ast: AST  = parser.parse(rules_source)
  writeFileSync( join(/* __dirname,  */'test/example_output_ast.json'),  JSON.stringify(ast) )
  return ast

}


// internal function: exported only for unit test purposes
export function _compile_(ast: AST): any {
  if(  (ast.class as TokenClass) === TokenClass.OPERATOR ){
    // console.log("category", ast.category, ast)
    // console.log("neg momo momo op:", ast)
    if(ast.category === "unary"){ 

      if( ast.type==="fully_qualify" ) {
        return _compile_(ast.primary)
      }

      return op[ ast.type ]( 
        _compile_(ast.primary) 
      )
    } else if(ast.category === "tenary"){ 
      return op[ ast.type ](
        _compile_(ast.primary), 
        _compile_(ast.secondary), 
        _compile_(ast.tertiary)
      )      
    } else if(ast.category === "binary"){ 


      if( ast.type==="select" ) {
       
        return op[ ast.type ](
          _compile_(ast.primary), 
          ast.secondary.id
        )
      }

      return op[ ast.type ](
        _compile_(ast.primary), 
        _compile_(ast.secondary)
      )
      
    }

    throw "Opertator category unknown."

  }

  else 

  if(  (ast.class as TokenClass) === TokenClass.LITERAL ) 
    return ast.value

  else

  if(  (ast.class as TokenClass) === TokenClass.ITERABLE ) {
    
    switch (ast.type) {
      case "dictionary":

        return ast.list
        .map( ([k,v]) => [k.id, _compile_(v)] )
        .reduce( (t,h) => ({ ...t, [h[0]]: h[1] }), {} )


      case "map":
        return new Map( 
          ast.list
          .map( ([k,v]) => [_compile_(k), _compile_(v)] )
        ) 

      case "list":
        return ast.list.map(_compile_)     
    }

    throw "AST `ITERABLE` must be of `type` identical to  `dictionary`,`map` or `list`"

  }

  else 
  
  if(  (ast.class as TokenClass) === TokenClass.IDENTIFIER ) {
    // if (!ctx) {
    //   console.error("Missing Context for Ident. AST:", ast)
    //   throw "Context for IDENTIFIER is not available"
    // }
    
    

    return ( ctx ) => ctx[ast.id]
  }
  
  else 

  if(  (ast.class as TokenClass) === TokenClass.SERVICE ) {
    const matches: Match[] = (ast.matches as AST[]).map( _compile_ ) 
    return new Service(ast.type, matches);
  } 
  
  else 
  
  if(  (ast.class as TokenClass) === TokenClass.CHILD ) {
    
    if (ast.type === 'match'){
      
      const children: Children = (ast.children as AST[]).map( _compile_ ) 
      return new Match(
        ast.route, 
        ((children || []) as Allow[]).filter(c => c.constructor.name === Allow.name), 
        ((children || []) as Match[]).filter(c => c.constructor.name === Match.name)  
      );
    }

    if (ast.type === 'allow'){
      // console.log("ast.actions", ast)
      return new Allow(ast.actions, _compile_(ast.condition)) as Allow;
    }

    throw "`Child` tokens must be of `type=match` or `type=allow`"
    
  } 
      

  throw "Token type unknown"

}

export default function( rules_source: string, js = false ): ACL{
  // not js then compile using CEL DSL
  if (js) return (eval(rules_source) as Service).acl
  const out = _compile_( parse(rules_source) )
  // console.log("compiled out: ", (( out as Service).acl[0].allows[0] as any).condition())
  return ( out as Service).acl
}