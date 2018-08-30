import { readFileSync, writeFileSync } from "fs";
import * as peg  from "pegjs";
import {join} from 'path'

console.log("Momo JIT")
const grammerSource = `
  ${readFileSync(join(__dirname, './fire.grammer.pegjs'), { encoding: "utf8"})}

  ${readFileSync(join(__dirname, './cel.grammer.pegjs'), { encoding: "utf8"})}
`
const parser = peg.generate(grammerSource, {
    allowedStartRules: [ "Service", "Expression" ],
    dependencies: {},
    output: "parser",


 
})


export = parser

