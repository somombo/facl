import { ACL, Service,  Match, Allow, Children} from "./parser/ast";
import './parser' 

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
  // writeFileSync( join(/* __dirname,  */'test/example_output_ast.json'),  JSON.stringify(ast) )
  return ast

}


// internal function: exported only for unit test purposes
export function _compile_(ast: AST): any {



  
  if(  TokenClass.SERVICE === (ast.class as TokenClass)  ) {

    const matches: Match[] = (ast.matches as AST[]).map( _compile_ ) 
    return new Service(ast.type, matches)

  } else if (  TokenClass.CHILD === (ast.class as TokenClass)  ) {
    
    if (ast.type === 'match'){
      
      const children: Children = (ast.children as AST[]).map( _compile_ ) 
      return new Match(
        ast.route, 
        ((children || []) as Allow[]).filter(c => c.constructor.name === Allow.name), 
        ((children || []) as Match[]).filter(c => c.constructor.name === Match.name)  
      )

    }

    if (ast.type === 'allow') {
    
      return new Allow(ast.actions, _compile_(ast.condition)) as Allow;
    }

    throw "`Child` tokens must be of `type=match` or `type=allow`"
    
  } 
  else 
  
  if(  TokenClass.OPERATOR === (ast.class as TokenClass)  ){

    
    if(ast.category === "unary"){ 

      if( ast.type==="fully_qualify" ) {
        return _compile_(ast.primary)
      }

      return op[ ast.type ]( 
        _compile_(ast.primary) 
      )

    } else if(ast.category === "binary") { 

      
      if( ast.type==="select" ) {
        
        return op[ ast.type ](
          _compile_(ast.primary), 
          ctx => ast.secondary.id
        )
      }

      return op[ ast.type ](
        _compile_(ast.primary), 
        _compile_(ast.secondary)
      )
      
    }

    throw "Opertator category unknown."

  } else if(ast.category === "tenary") { 

    return op[ ast.type ](
      _compile_(ast.primary), 
      _compile_(ast.secondary), 
      _compile_(ast.tertiary)
    )

  } else if (  TokenClass.LITERAL === (ast.class as TokenClass)  ) {

    return ctx => ast.value

  } else if (  TokenClass.ITERABLE === (ast.class as TokenClass)  ) {
    
    switch (ast.type) {
      case "dictionary":

        return ctx => ast.list
        .map( ([k,v]) => [k.id, _compile_(v)(ctx)] )
        .reduce( (t,h) => ({ ...t, [h[0]]: h[1] }), {} )


      case "map":
        return ctx => {
        
          
          const m = new Map( 
          ast.list
            .map( ([k,v]) => [_compile_(k)(ctx), _compile_(v)(ctx)] )
        ) 
          return m
    
  }
      case "list":
        return ctx => ast.list.map(i => _compile_(i)(ctx))     
  } 
  
    throw "AST `ITERABLE` must be of `type` identical to  `dictionary`,`map` xor `list`"
      
  } else if (  TokenClass.IDENTIFIER === (ast.class as TokenClass)  ) {

    return ctx => ctx[ast.id] 
    }

      

  throw new Error("Token type unknown")

}

export default function( rules_source: string, js = false ): ACL{
  // not js then compile using CEL DSL
  if (js) return (eval(rules_source) as Service).acl
  const ast = parse(rules_source)


  const out = _compile_( ast )

  return ( out as Service ).acl
}