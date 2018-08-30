import * as express from 'express';
import facl from '../src';

import { join } from 'path';
import { readFileSync } from 'fs'
import * as errorhandler from 'errorhandler'
import { json, raw, text, urlencoded } from 'body-parser'

export default function(rules_path: string, parseBody = true) {

  const app = express()

  if(parseBody) {

    app.use(json())
    app.use(raw())
    app.use(text())
    app.use(urlencoded({ extended: true }))

  }

  app.use(facl( readFileSync(join(__dirname, rules_path), { encoding: "utf8"}) ))
  
  

  
  
  app.use(errorhandler())
  
  
  app.all('*', (req, res) => res.send(`<h1>Congratulations!</h1> <h4>You are authorized to see this.</h4> <pre>${Date.now()}</pre>`))
  
  // return require('firebase-functions').https.onRequest(app)
  return app
  
}

