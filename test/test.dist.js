

const express = require('express');
const facl = require('../src/index').default;

const { join } = require('path');
const { readFileSync } = require('fs')
const errorhandler = require('errorhandler')
const { json, raw, text, urlencoded } = require('body-parser')

// const app = makeApp('/example.service.js')
// const rules_path= '/example.service.js'
// const rules_path= '/example.nocomments.rules'
const rules_path= '/example.simple.rules'



const app = express()

 //   app.use(json())
 //   app.use(raw())
 //   app.use(text())
 //   app.use(urlencoded({ extended: true }))

 const rules_source = readFileSync(join(__dirname, '../test',rules_path), { encoding: "utf8"});


  app.use(facl( rules_source ))
  

  
  
  app.use(errorhandler())
  
  
  app.all('*', (req, res) => res.send(`<h1>Congratulations!</h1> <h4>You are authorized to see this.</h4> <pre>${Date.now()}</pre>`))
  


 const PORT = process.env.PORT || 3000
 app.listen(PORT, () => {
   console.log(`Example app listening on port ${PORT}!`)
 })