// {  function __cel$ltr__(head, tail){ return tail.reduce( (t,h) => ({...h, primary: t}), head) }  }
// LTR Function TODO: Comment out. Must only be in `fire.grammer.pegjs` file
/* left is `primary` and right is `secondary` operand. */ 
/* Third operand is `tertiary` */

/* 
Cel Grammer

Ported from https://github.com/google/cel-spec/blob/master/doc/langdef.md

By Chisomo Sakala (c) 2018

*/



start = Expression

//////////////////////////////////////////////////
///////////     Data Structures 
//////////////////////////////////////////////////

  
List // "ExprList"
  = all:
  (
    head:Expression __ tail:("," __ e:Expression {return e})* 
    { return { class: "ITERABLE", type: "list", list: [head, ...tail] } }
  )? 
  { return all ? all : { class: "ITERABLE", type: "list", list: [] }}

Dictionary // "FieldInits"
  = all:
  (
    head:(k:IDENTIFIER __ ":" __ v:Expression {return [k,v]}) __ 
    tail:("," __ k:IDENTIFIER __ ":" __ v:Expression {return [k,v]})* 
    { return { class: "ITERABLE", type: "dictionary", list: [head, ...tail] } }    
  )? 
  { return all ? all : { class: "ITERABLE", type: "dictionary", list: [] }}

Map // "MapInits"
  = all:
  (
    head:(k:Expression __ ":" __ v:Expression {return [k,v]}) __ 
    tail:("," __ k:Expression __ ":" __ v:Expression {return [k,v]})*
    { return { class: "ITERABLE", type: "map", list: [head, ...tail] } }
  )? 
  { return all ? all : { class: "ITERABLE", type: "map", list: [] }}








//////////////////////////////////////////////////
///////////     Expressions
//////////////////////////////////////////////////


Expression // "Common Expression" i.e. CEL
  = t:Disjunction __ "?" __ s:Expression __ ":"  __ p:Expression
	{ return {class: "OPERATOR", type: "conditional", category:"tenary", primary:p, secondary:s, tertiary:t} }    
  / Disjunction


Disjunction // "OR"
  = head:Conjunction tail:(DisjunctionOperation)* { return __cel$ltr__(head, tail) } 
DisjunctionOperation
  = __ "||" __ secondary:Conjunction 
  { return {class: "OPERATOR", type:"or", category:"binary", secondary} }


Conjunction // "AND"
  = head:Relation tail:(ConjunctionOperation)* { return __cel$ltr__(head, tail) } 
ConjunctionOperation
  = __ "&&" __ secondary:Relation 
  { return {class: "OPERATOR", type:"and", category:"binary", secondary} }


Relation // >,<,= etc
  = head:Addition tail:(RelationOperation)* { return __cel$ltr__(head, tail) } 
RelationOperation
  = __ type:RELATION_SYMBOL __ secondary:Addition 
  { return {class: "OPERATOR", type, category:"binary", secondary} }
RELATION_SYMBOL      
  = "<" {return 'less'}
  / "<=" {return 'lessOrEqual'}
  / ">=" {return 'greaterOrEqual'}
  / ">" {return 'greater'}
  / "==" {return 'equal'}
  / "!=" {return 'notEqual'}
  / " in " {return 'in'}

Addition // +,-
  = head:Multiplication tail:(AdditionOperation)* { return __cel$ltr__(head, tail) } 
AdditionOperation
  = __ type:SUM_SYMBOL __ secondary:Multiplication 
  { return {class: "OPERATOR", type, category:"binary", secondary} }
SUM_SYMBOL
  = "+" {return 'add'}
  / "-" {return 'subtract'}


Multiplication // *,/,%
  = head:Unary tail:(MultiplicationOperation)* { return __cel$ltr__(head, tail) } 
MultiplicationOperation
  = __ type:PRODUCT_SYMBOL __ secondary:Unary 
  { return {class: "OPERATOR", type, category:"binary", secondary} }
PRODUCT_SYMBOL
  = "*" {return 'multiply'}
  / "/" {return 'divide'}
  / "%" {return 'remainder'}

Unary      
  = ("!" __)+ primary:Member { return {class: "OPERATOR", type: "not", category:"unary", primary} }
  / ("-" __)+ primary:Member { return {class: "OPERATOR", type: "negative", category:"unary", primary} }
  / Member


Member
  = head:(LITERAL / Atomic) tail:(MemberOperation)* { return __cel$ltr__(head, tail) }
MemberOperation
  = __ "." __ secondary:Atomic { return { class: "OPERATOR", type:"select", category:"binary", secondary } }
  / __ "[" __ secondary:Expression __ "]" { return { class: "OPERATOR", type:"index", category:"binary", secondary } }
  / __ "{" __ secondary:Dictionary __ "}" { return { class: "OPERATOR", type:"construct", category:"binary", secondary } }
  / __ "(" __ secondary:List __ ")" { return { class: "OPERATOR", type:"invoke", category:"binary", secondary } }
 
 
Atomic
  = "[" __ exprList:List __ "]" { return exprList }
  / "{" __ mapInits:Map __ "}" { return mapInits }
  / "(" __ expr:Expression __ ")" { return expr }
  / "." __ primary:IDENTIFIER { return {class: "OPERATOR", type: "fully_qualify", category:"unary", primary}}
  / IDENTIFIER





////////////////////////////////////
///   Literals
///////////////////////////////////




IDENTIFIER
  = (!RESERVED / RESERVED) [_a-zA-Z][_a-zA-Z0-9]*
  { return {class: "IDENTIFIER", id: text()} }
  

LITERAL
  = value:FLOAT_LIT { return { class: "LITERAL", type: "double", value } }
  / value:UINT_LIT { return { class: "LITERAL", type: "uint", value } }
  / value:INT_LIT { return { class: "LITERAL", type: "int", value } }
  / value:BYTES_LIT { return { class: "LITERAL", type: "bytes", value } } // important: check for bytes before string 
  / value:STRING_LIT { return { class: "LITERAL", type: "string", value } } 
  / value:BOOL_LIT { return { class: "LITERAL", type: "bool", value } } 
  / value:NULL_LIT { return { class: "LITERAL", type: "null_type", value } }

INT_LIT
  = "0x" HEXDIGIT+ { return parseInt(text(), 16) }
  / DIGIT+ { return parseInt(text(), 10) }
  

UINT_LIT     
  = int:INT_LIT [uU] { return Math.abs(int) }

FLOAT_LIT    
  = DIGIT* "." DIGIT+ EXPONENT? 
  / DIGIT+ EXPONENT { return parseFloat(text())}

DIGIT
  = [0-9]

HEXDIGIT
  = [0-9abcdefABCDEF]

EXPONENT
  = [eE] [+-]? DIGIT+

BYTES_LIT
  = [bB] str:STRING_LIT { return Uint8Array.from(  str.split("").map( c=>c.codePointAt(0) )  )}

STRING_LIT   
  = // BYTES_LIT /
  raw:[rR]? str:(
    '"""' str:( !( '"""' ) (ESCAPE / .) )* '"""' { return str.map( t => t[1] ) }
    / "'''" str:( !( "'''" ) (ESCAPE / .) )* "'''" { return str.map( t => t[1] ) }
    / '"' str:( !( '"'  / NEWLINE ) (ESCAPE / .) )* '"'   { return str.map( t => t[1] ) }
    / "'" str:( !( "'"  / NEWLINE ) (ESCAPE / .) )* "'" { return str.map( t => t[1] ) } 
  ) { return str.map( c => (raw && c.rawVal) ? c.rawVal : c.toString()).join("") } 

ESCAPE     
  = "\\" eskey:$[bfnrt"'\\] {
      const strVal = ({
        'b': "\b",
        'f': "\f",
        'n': "\n",
        'r': "\r",
        't': "\t",
        '"': "\"",
        '\'': "\'",
        '\\': "\\"
      })[eskey]
      
	  const numVal = strVal.codePointAt(0)
      
      if(!eskey) throw "escape char error";
      return ({ 
          type: "escapeChar", 
          toString: () => strVal, 
          rawVal: text()
      })
    }
  / "\\" "u" hx:$(HEXDIGIT HEXDIGIT HEXDIGIT HEXDIGIT) { 
  		const numVal = parseInt(hx,16)
  		return ({ 
        	type: "escapeChar", 
            toString: () => String.fromCodePoint(numVal), 
            rawVal: text()
        }) 
     }
  / "\\" oct:$([0-3] [0-7] [0-7]) { 
  		const numVal = parseInt(oct,8)
  		return ({ 
        	type: "escapeChar", 
            toString: () => String.fromCodePoint(numVal), 
            rawVal: text()
        }) 
   	}

NEWLINE
  = "\r\n"
  / "\r"
  / "\n"

BOOL_LIT
  = ("true" / "false") { return text()==="true" ? true : false }

NULL_LIT
  = "null" { return null }

RESERVED
  = BOOL_LIT 
  / NULL_LIT 
  / "in"
  / "for" 
  / "if" 
  / "function" 
  / "return" 
  / "void"
  / "import" 
  / "package" 
  / "as" 
  / "let" 
  / "const"


////////////////////////////////////////////////////
/////       Ignorables
//////////////////////////////////////////////////////

_ "Space"
  = [ \t]*
  // = [ \t]+ 
  
Whitespace "Whitespace"
  = [ \t\n\r]*
  // = [\t\n\f\r ]+ 

_$ "Comment"
  = '//' $(!NEWLINE .)* NEWLINE? {return { class: "COMMENT", type: "single" }}

MultiLineComment "Multi-line Comment"  
  = '/*' $(!'*/' .)* '*/'  {return { class: "COMMENT", type: "multi" }}

__
  = Whitespace MultiLineComment? Whitespace

////////////////////////////////////////////////////////
