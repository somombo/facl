
const { readFile, writeFile } =  require('fs')

const { mkdirp } = require( 'mkdirp' );
    
const { join } = require('path')
const { generate } = require('pegjs')

readFile(join(/* __dirname, */ 'src', '/parser/cel.grammer.pegjs'), "utf8", (err, cel_source) => {

  if (err) {
    console.warn( "Could not read 'cel.grammer.pegjs'\n\n" );
    throw err;
  }

  let grammerSource = cel_source

  readFile(join(/* __dirname, */ 'src', '/parser/fire.grammer.pegjs'), "utf8", (err, fire_source) => {

    if (err) {
      console.warn( "Could not read 'fire.grammer.pegjs'\n\n" );
      throw err;
    }
    
    grammerSource += ('\n\n' + fire_source)

    const parser = generate(grammerSource, {
      allowedStartRules: [ "Service", "Expression" ],
      // output: "parser",
      format: "commonjs",
      output: "source",
      dependencies: {},
    }) 

    mkdirp(join(/* __dirname, */ 'dist'),  err => {
      if (err) {
        console.error( "Could not create directory 'dist'\n\n" );
        throw err;
      }
      
      writeFile(join(/* __dirname, */ 'dist', 'parser/index.js'), parser, 'utf8', (err) => {    
        
        
        if (err) {
          console.error( "Could not save file to 'dist/parser.js'\n\n" );
          throw err;
        }  
        console.log( "The parser successfully has been saved to 'dist/parser.js'\n\n" );
      
   
  
      })  
    })


  })
})
