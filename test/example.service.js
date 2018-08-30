const { service, match, allow } = require('../src/parser/ast')

service('https.cloudfunction.net',

  match('/app', 

    match('/my_apis/{api}/endpoints', 
      match('/{endpoint=**}', 

        allow('read, write', request => (request).auth.uid !== null),

      )
    ),

    allow('read', _ => true),

    match('/other_api/{other_endpoint}', 

      allow('get', request => !!request.accepts('json')),
      allow('post, put, delete', request => {
        // console.log(request.body, (request as any).rawBody)
        return !request.body
      }),

    ),

  ),  

)