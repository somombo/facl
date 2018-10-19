import * as express from 'express';
import * as facl from '../src';

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

  app.use( facl.fromFile(rules_path) )
  
  

  
  
  app.use(errorhandler())
  
  
  app.all('*', (req, res) => res.send(`<h1>Congratulations!</h1> <h4>You are authorized to see this.</h4> <pre>${Date.now()}</pre>`))
  
  // return require('firebase-functions').https.onRequest(app)
  return app
  
}

