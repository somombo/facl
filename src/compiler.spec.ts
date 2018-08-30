
import { expect } from 'chai';
import 'mocha';

import {_compile_ as compile} from './compiler'


describe('Compile AST of cel expression', () => {

  it('should perform simple binary arithmetic', () => {
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

  it('should perform simple binary arithmetic', () => {
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
  });



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