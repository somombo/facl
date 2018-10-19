// exports.app = require('firebase-functions').https.onRequest(app);


// import { hello } from './hello-world';
// import { expect } from 'chai';
import * as request from 'supertest';

import 'mocha';
import makeApp from './app';


import { Buffer } from 'buffer'
import {READ_METHODS,WRITE_METHODS} from '../src/utils'
import { join } from 'path';

const METHODS = [...READ_METHODS,...WRITE_METHODS]


// const app = makeApp('/example.service.js')
// const rules_path= '/example.service.js'
// const rules_path= '/example.nocomments.rules'
const rules_path= '/example.simple.rules'
const app = makeApp( join(__dirname, rules_path))

if(global["describe"]){ // TODO: find better test for running in mocha environment

describe('## Beginning Example API Integration Testing ...', function() {


  describe('/app', function() { 
    describe('#read,write', function() { 

      it("should allow read", async function() { 

        
          await request(app) 
          .get('/app')
          // .set('Accept', 'application/json')
          // .expect('Content-Type', /json/)
          .expect(200)
          


      });

      it("should *not* allow write", async function() { 
        const rawBody:string = "Hello There World!"
        const contentLength = `${Buffer.byteLength(rawBody)}`
        

          await request(app) 
          .post('/app')
          .send(rawBody)
          .set('Content-Type', 'text/plain;charset=UTF-8')
          .set('Content-Length', contentLength )  
          .expect(401)

      });
    })

    
    
    describe('./my_apis/{api}/endpoints',  function() { 
      describe('#no_requests',  function() { 
        for (const method of METHODS) {
          
          it(`should deny ${method.toUpperCase()} request`, async function() { 
            // const rawBody:string = "Hello There World!"
            // .send(rawBody)
            // .set('Content-Type', 'text/plain;charset=UTF-8')
            // .set('Content-Length', `${Buffer.byteLength(rawBody)}` )              
            const path = '/app/my_apis/darn_good_api/endpoints'

            await request(app)[method.toLowerCase()](path)
            // .send(rawBody)
            // .set('Content-Type', 'text/plain;charset=UTF-8')
            // .set('Content-Length', `${Buffer.byteLength(rawBody)}` )  
            // .expect('Content-Type', /json/)
            .expect(401)
    
          
          });
        }

      })




      describe('./{endpoint=**}', function() { 
        describe('if auth valid', function() { 

          it('should be able to read', async function() { 
            await request(app) 
            .get('/app/my_apis/kinda_good_api1/endpoints/any/other/endpoint')
            .set('Authorization', 'Bearer 4321')      
            .set('Accept', 'application/json')
            .expect(200)


          });

          it('should be able to write', async function() { 
            await request(app) 
            .post('/app/my_apis/kinda_good_api2/endpoints/any/other/endpoint')
            .send({ foo: "bar"})
            // .set('Content-Type', 'text/plain;charset=UTF-8')
            // .set('Content-Length', `${Buffer.byteLength(rawBody)}` )        
            .set('Accept', 'application/json')
            .set('Authorization', 'Bearer 4321')
            .expect(200)
          });
        })
        
      });      
      
    });

    describe('./other_api/{other_endpoint}', function() { 
      describe('if Content-Type is:', function() {
        it('valid then allow', async function() { 
          await request(app) 
          .patch('/app/other_api/awesome_endpoint')
          .send({ foo: "bar"})
          .set('Content-Type', 'application/json')
          .expect(200)
  
  
        });

        it('invalid then deny', async function() { 

          
          await request(app) 
          .patch('/app/other_api/awesome_endpoint')
          .set('Content-Type', 'text/plain;charset=UTF-8')
          .expect(401)
  
  
        });
      })


      describe('if has body, ', function() { 

        it('should be able to POST', async function() { 
          await request(app) 
          .post('/app/other_api/awesome_endpoint')
          .send({ foo: "bar1"})
          // .set('Accept', 'application/json')
          // .expect(200)

    
        });

        it('should be able to PUT', async function() { 
          await request(app) 
          .put('/app/other_api/awesome_endpoint')
          .send({ foo: "bar2"})
          // .set('Accept', 'application/json')
          .expect(200)

    
        });

        it('should be able to DELETE', async function() { 
          await request(app) 
          .delete('/app/other_api/awesome_endpoint')
          .send({ foo: 1})
          .set('Accept', 'application/json')
          .expect(200)

    
        });
        
        
      });
        

      
    });
    
  });



});


} else {

  const PORT = process.env.PORT || 3000
  app.listen(PORT, () => {
    console.log(`Example app listening on port ${PORT}!`)
  })  
}





