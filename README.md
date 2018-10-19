# FACL

This is a firebase rules inspired access control language (DSL) for securing backend REST api's written in node.js. 

It is based on firebase' security rule syntax.

- See [Cloud Storage Security Rules Ref](https://firebase.google.com/docs/reference/security/storage/) and [Firestore Security Rules Ref](https://firebase.google.com/docs/firestore/security/rules-conditions)

- Also checkout [Google Cel Spec](https://github.com/google/cel-spec), for the expression language's specification.


This project aims to provide a similar and consistent syntax as that exemplified at the links above.

## Installation / Running

To install run:
```
$ npm install facl
```

## Usage
 Use as expressjs middleware created from directly from inline source code like:
```js
 import * as facl from 'facl'
 app.use(facl.fromSource(`
   service https.cloudfunctions.net {
     match /path { 
       allow read: if true;
     }
   }
 `));
 // will allow HTTP GETs but not POSTs at '/path'
```
 

Alternatively, you can pull in the rules from a local file as in:

```js
 const facl = require('facl') // feel free to use commonjs
 app.use(facl.fromFile('/path/to/example.simple.rules'))
```

 The functions `fromSource` and `fromFile` are only intended to be used for development purposes.
 
 In production, simply store the rules in memory (as a string) in the `FACL_ACCESS_CONTROL_RULES` environment variable and then:

```ts 
 import facl from 'facl' // Then import default for production. Or do commonjs equivalent 
 app.use(facl()) // Alternatively, you can pass in a custom env. varName e.g `facl('MY_ENV_VAR')`
```

> Take a look at the file `example.app.js` for a basic example of how to use this lib.
> To the run example:
> ```
> $ node node_modules/facl/example.app.js
> ```



## Further Info
Here is an example of what we are aiming to be able to write with this language. This would be for the purpose of securing or controlling access to REST endpoints in a firebase cloud functions context:

```
// The `cloud.functions.https` namespace currently doesn't exist but would 
// allow things like `request.accepts("json")` and `request.body`
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
      // only if requester's `Content-Type` is "application/json".    
      // The `allow get` is the same as `allow read`.
      allow get: if request.accepts("json");  
          
      // Allow POST, PUT and DELETE requests to e.g. "/other_api/my_google_plus",
      // only if requester's has non-empty body.
      // The "allow post, put, delete" is the same as `allow write`.
      allow post, put, delete: if request.body != null;  
    
    }     
  }

  // all requests to anything that's not explicitly declared with `match` will be denied by default
}
```


Feel free to star / fork  or open an issue if you have any questions!

Related project [XACML](https://en.wikipedia.org/wiki/XACML)