
const EXAMPLE_AC_RULES = (`
  // The \`cloud.functions.https\` namespace currently doesn't exist but would 
  // allow things like \`request.is("json")\` and \`request.body\`
  // that are expected in an http validation context (see below for example use)
  service cloud.functions.https {
    match /app {

      // Allow all requests to e.g. "/my_apis/my_twitter/endpoints/my_followers_list",
      // only if user (i.e. requester) is signed in, 
      // and deny all requests to e.g. "/non_apis/my_twitter/non_endpoints/my_followers_list".
      // even if user is signed in.
      match /my_apis/{api}/endpoints {
        match /{endpoint=**} {
          allow read, write: if request.auth.uid != null;
        }
      }

      allow read: if true; // e.g. Anyone can execute "GET /app"

      match /other_api/{other_endpoint} {
        
        // Allow GET requests to e.g. "/other_api/my_youtube",
        // only if requester's \`Content-Type\` is "application/json".    
        // The \`allow get\` is the same as \`allow read\`.
        allow get: if request.is("json");  
            
        // Allow POST, PUT and DELETE requests to e.g. "/other_api/my_google_plus",
        // only if requester's has non-empty body.
        // The "allow post, put, delete" is the same as \`allow write\`.
        allow post, put, delete: if request.body != null;  
      
      }     
    }
  
    // all requests to anything that's not explicitly declared with \`match\` will be denied by default
  }
`)

const express = require('express')
const app = express()

// takes in string source code representing the rules
// returns AST or similar data structure respresenting the syntactic analysis
function fake_ac_rules_parse(rules){
  return rules.length
}

// **currently only a mock function
// will depend on a parse function e.g. `ac_rules_parse` 
// that hopefully provided by third party or firebase team
function ac_middleware(rules){
  return (req, res, next) => {
    function isAllowed (req) {

      // this fake mock makes it so that it currently 'randomly' allows or denys 
      const fake_decision = !!((Date.now() + JSON.stringify(req.headers).length + fake_ac_rules_parse(rules))  % 2)
      return fake_decision

    } 
  
    if( !isAllowed(req) ) {  
      res.status(401).json({ error: "Not Authorized", status: 401, time: Date.now()})
      return;
    } 
  
    next();
  }
  
}
 
app.use(ac_middleware(EXAMPLE_AC_RULES))

app.all('*', (req, res) => res.send(`<h1>Congratulations!</h1> <h4>You are authorized to see this.</h4> <pre>${Date.now()}</pre>`))

const PORT = process.env.PORT || 3000
app.listen(PORT, () => {
  console.log(`Example app listening on port ${PORT}!`)
})

// exports.app = require('firebase-functions').https.onRequest(app);
