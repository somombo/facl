

const express = require('express');
const facl = require('./dist/index').default;
const { json, raw, text, urlencoded } = require('body-parser') 

const app = express()



 const rules_source = `
  service https.cloudfunctions.net {
    match /app {

      match /my_apis/{api}/endpoints {
        match /{endpoint=**} {
          allow read, write: if request.auth.uid != null;
        }
      }
      /* multi-line comments now supported */
      allow read: if true; 

      match /other_api/{other_endpoint} {
      
        allow patch: if request.is("json");  
          
        allow post, put, delete: if request.body != null;  
      
      }     
    }

  }
 `

  app.use(json())
  app.use(raw())
  app.use(text())
  app.use(urlencoded({ extended: true }))

  app.use(facl( rules_source )) // <-- this is how it works
  

  
  
  // app.use(require('errorhandler')()) // optional error independent error handling plugin
  
  
  app.all('*', (req, res) => res.send(`<h1>Congratulations!</h1> <h4>You are authorized to see this.</h4> <pre>${Date.now()}</pre>`))
  


 const PORT = process.env.PORT || 3000
 app.listen(PORT, () => {
   console.log(`Example app listening on port ${PORT}!`)
 })