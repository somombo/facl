# FACL

This is an access control language (DSL) for securing backend REST api's written in node.js. 

It is based on firebase' security rule syntax.

- See [Cloud Storage Security Rules Ref](https://firebase.google.com/docs/reference/security/storage/)

- See [Firestore Security Rules Ref](https://firebase.google.com/docs/firestore/security/rules-conditions)

This project aims to provide a similar and consistent syntax as that exemplified at the links above.

Here is an example of what we are aiming to be able to write with this language. This would be for the purpose of securing or controlling access to REST endpoints in a firebase cloud functions context:

```
// The `cloud.functions.https` namespace currently doesn't exist but would 
// allow things like `request.is("json")` and `request.body`
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
      allow get: if request.is("json");  
          
      // Allow POST, PUT and DELETE requests to e.g. "/other_api/my_google_plus",
      // only if requester's has non-empty body.
      // The "allow post, put, delete" is the same as `allow write`.
      allow post, put, delete: if request.body != null;  
    
    }     
  }

  // all requests to anything that's not explicitly declared with `match` will be denied by default
}
```


See also [XACML](https://en.wikipedia.org/wiki/XACML).