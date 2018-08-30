
import { expect } from 'chai';
import 'mocha';

import {_compile_ as compile} from './compiler'


describe('Compilation AST:', () => {
  
  describe('for el expressions', () => {



    describe('Arithmetic:', () => {
      
      
        it('should resolve simple positibe integer', () => {
          const ast: any = {
            "class": "LITERAL",
            "type": "int",
            "value": 3
          }
      
          expect(compile(ast)).to.equal(3);
        });
      
        it('should resolve negative integer', () => {
      
          const value = compile({
            "class": "OPERATOR",
            "type": "negative",
            "category": "unary",
            "primary": {
               "class": "LITERAL",
               "type": "int",
               "value": 1
            }
         } as any)
      
          expect(value).to.equal(-1);
        });
      
        it('should perform simple binary operation', () => {
          const ast: any = {
            "class": "OPERATOR",
            "type": "remainder",
            "category": "binary",
            "secondary": {
               "class": "LITERAL",
               "type": "int",
               "value": 5
            },
            "primary": {
               "class": "LITERAL",
               "type": "int",
               "value": 7
            }
          }
      
          expect(compile(ast)).to.equal(2);
        })
  
  
        it('should calculate complex arithmetic', () => {
          const ast: any = {
            "class": "OPERATOR",
            "type": "multiply",
            "category": "binary",
            "secondary": {
               "class": "OPERATOR",
               "type": "negative",
               "category": "unary",
               "primary": {
                  "class": "LITERAL",
                  "type": "int",
                  "value": 11
               }
            },
            "primary": {
               "class": "OPERATOR",
               "type": "subtract",
               "category": "binary",
               "secondary": {
                  "class": "OPERATOR",
                  "type": "remainder",
                  "category": "binary",
                  "secondary": {
                     "class": "LITERAL",
                     "type": "int",
                     "value": 2
                  },
                  "primary": {
                     "class": "LITERAL",
                     "type": "int",
                     "value": 11
                  }
               },
               "primary": {
                  "class": "OPERATOR",
                  "type": "add",
                  "category": "binary",
                  "secondary": {
                     "class": "LITERAL",
                     "type": "int",
                     "value": 3
                  },
                  "primary": {
                     "class": "LITERAL",
                     "type": "int",
                     "value": 7
                  }
               }
            }
         }
      
      
          expect(compile(ast)).to.equal(-99);
        });      
    });
  
  
    describe('Atomics elements', () => {
      it('should resolve a Mapping ', () => {
        const ast: any = {
          "class": "ITERABLE",
          "type": "map",
          "list": [
             [
                {
                   "class": "OPERATOR",
                   "type": "less",
                   "category": "binary",
                   "secondary": {
                      "class": "LITERAL",
                      "type": "int",
                      "value": 7
                   },
                   "primary": {
                      "class": "LITERAL",
                      "type": "int",
                      "value": 2
                   }
                },
                {
                   "class": "LITERAL",
                   "type": "int",
                   "value": 3142
                }
             ],
             [
                {
                   "class": "OPERATOR",
                   "type": "add",
                   "category": "binary",
                   "secondary": {
                      "class": "LITERAL",
                      "type": "string",
                      "value": "world"
                   },
                   "primary": {
                      "class": "LITERAL",
                      "type": "string",
                      "value": "hello"
                   }
                },
                {
                   "class": "LITERAL",
                   "type": "int",
                   "value": 29
                }
             ]
          ]
       }
    
        expect(compile(ast)).to.deep.equal(
          new Map([ [true,3142], ["helloworld", 29] ] as any) 
        );
      });      
    });
  
    describe('Field selection and Identifiers', () => {
      // for foo.bar.wow or .foo.bar.wow
      const ctx = {
        "foo": {
          "bar": {
            "wow": 133
          }
        },
        "ok": "hello",
        "another": {
          "one": 6
        },
        "mylist": "abcdefg".split(""),
        "myFunc": function(str, num){
          return `I made this: ${(str.length + num)}`  
        },
        "MyMessage": class {
          public greeting
          public age
          constructor({greeting, age}){
            this.greeting = greeting
            this.age = age
          } 
          combine(){
            return `Uli, ${this.greeting} ${this.age}`
          }
        }     
      
      }
  
      it('should resolve Identifier', () => {
    
        // from ok
        const ast: any = {
          "class": "IDENTIFIER",
          "id": "ok"
       }
    
        expect(compile(ast)(ctx)).to.equal("hello");
      })
  
      it('should select Identifier property', () => {
    
        // p = ctx => ctx["another"]
        // s = "one"
        // o = ctx => (ctx["another"])["one"]

        // from another.one
        const ast: any = {
          "class": "OPERATOR",
          "type": "select",
          "category": "binary",
          "secondary": {
             "class": "IDENTIFIER",
             "id": "one"
          },
          "primary": {
             "class": "IDENTIFIER",
             "id": "another"
          }
        }
        const output = compile(ast)(ctx)
      //  console.log("compile ast for prop", output)
    
        expect(output).to.equal(6);
      })
  
      it('should select Literal property', () => {
    
        // p = ctx => ctx["another"]
        // s = "one"
        // o = ctx => (ctx["another"])["one"]

        // input: "The World".length
        const ast: any = {
          "class": "OPERATOR",
          "type": "select",
          "category": "binary",
          "secondary": {
             "class": "IDENTIFIER",
             "id": "length"
          },
          "primary": {
             "class": "LITERAL",
             "type": "string",
             "value": "The World"
          }
       }
        const output = compile(ast)
      //  console.log("compile ast for prop", output)
    
        expect(output).to.equal(9);
      })
  
      it('should resolve relative field selection', () => {
    
        // from foo.bar.wow
        const ast: any = {
          "class": "OPERATOR",
          "type": "select",
          "category": "binary",
          "secondary": {
             "class": "IDENTIFIER",
             "id": "wow"
          },
          "primary": {
             "class": "OPERATOR",
             "type": "select",
             "category": "binary",
             "secondary": {
                "class": "IDENTIFIER",
                "id": "bar"
             },
             "primary": {
                "class": "IDENTIFIER",
                "id": "foo"
             }
          }
       }
    
        expect(compile(ast)(ctx)).to.equal(133);
      })
  
      it('should resolve fully qualified field selection', () => {
    
        // from .foo.bar.wow
        const ast: any = {
          "class": "OPERATOR",
          "type": "select",
          "category": "binary",
          "secondary": {
             "class": "IDENTIFIER",
             "id": "wow"
          },
          "primary": {
             "class": "OPERATOR",
             "type": "select",
             "category": "binary",
             "secondary": {
                "class": "IDENTIFIER",
                "id": "bar"
             },
             "primary": {
                "class": "OPERATOR",
                "type": "fully_qualify",
                "category": "unary",
                "primary": {
                   "class": "IDENTIFIER",
                   "id": "foo"
                }
             }
          }
       }
    
        expect(compile(ast)(ctx)).to.equal(133);
      })
      
      describe('index, invoke, construction', () => {
        
        it('should select from list by numerical index', () => {
    

  
          // from mylist[4]
          const ast: any = {
            "class": "OPERATOR",
            "type": "index",
            "category": "binary",
            "secondary": {
               "class": "LITERAL",
               "type": "int",
               "value": 4
            },
            "primary": {
               "class": "IDENTIFIER",
               "id": "mylist"
            }
         }
          const output = compile(ast)(ctx)
        //  console.log("compile ast for prop", output)
      
          expect(output).to.equal("e");
        }) 

        it('should invoke muilti-parameter function', () => {
    

  
          // from myFunc("bwanji",123)
          const ast: any = {
            "class": "OPERATOR",
            "type": "invoke",
            "category": "binary",
            "secondary": {
               "class": "ITERABLE",
               "type": "list",
               "list": [
                  {
                     "class": "LITERAL",
                     "type": "string",
                     "value": "bwanji"
                  },
                  {
                     "class": "LITERAL",
                     "type": "int",
                     "value": 123
                  }
               ]
            },
            "primary": {
               "class": "IDENTIFIER",
               "id": "myFunc"
            }
         }

          const output = compile(ast)(ctx)

      
          expect(output).to.equal("I made this: 129");
        }) 
        
        it('should construct muilti-parameter Message (Map)', () => {

          /* input:
          ``` 
            MyMessage { 
              greeting:"bwino",
              age:30
            }
          ```            
          */
          const ast: any = {
            "class": "OPERATOR",
            "type": "construct",
            "category": "binary",
            "secondary": {
               "class": "ITERABLE",
               "type": "dictionary",
               "list": [
                  [
                     {
                        "class": "IDENTIFIER",
                        "id": "greeting"
                     },
                     {
                        "class": "LITERAL",
                        "type": "string",
                        "value": "bwino"
                     }
                  ],
                  [
                     {
                        "class": "IDENTIFIER",
                        "id": "age"
                     },
                     {
                        "class": "LITERAL",
                        "type": "int",
                        "value": 30
                     }
                  ]
               ]
            },
            "primary": {
               "class": "IDENTIFIER",
               "id": "MyMessage"
            }
         }

          const output = compile(ast)(ctx)


          expect(output.combine()).to.equal("Uli, bwino 30");
        })       

      });
        
    });

  

  });
});