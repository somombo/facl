// exports.app = require('firebase-functions').https.onRequest(app);


import * as assert from 'assert';

// import { hello } from './hello-world';
import { expect } from 'chai';
import * as request from 'supertest';

import 'mocha';
import makeApp from './app';


console.log("Getting going..")
// const app = makeApp('/example.service.js')
// const rules_path= '/example.service.js'
// const rules_path= '/example.nocomments.rules'
const rules_path= '/example.simple.rules'
const app = makeApp(rules_path)

// const PORT = process.env.PORT || 3000
// app.listen(PORT, () => {
//   console.log(`Example app listening on port ${PORT}!`)
// })


describe('Example API Integration Tests', function() {

  
  describe('At /app ', function() { 

    it('should be able to read but not right', function(done) { 
      request(app) 
      .get('/app')
      .set('Accept', 'application/json')
      .expect(200)
      .end(function(err, res) {
        if (err) return done(err);
        // expect(res.body).to.be.an('array'); 
        // expect(res.body).to.be.empty; 
        done();
      })

    });
    
  });


  describe('At /app/my_apis/{api}/endpoints', function() { 

    it('should *not* be able to #read,write', function(done) { 
      request(app) 
      .get('/app/my_apis/darn_good_api/endpoints')
      .set('Accept', 'application/json')
      .expect(200)
      .end(function(err, res) {
        if (err) return done(err);
        // expect(res.body).to.be.an('array'); 
        // expect(res.body).to.be.empty; 
        done();
      })

    });
    
  });


  describe('At /app/my_apis/darn_good_api/endpoints/{endpoint=**} ', function() { 

    it('should be able to read if auth valid', function(done) { 
      request(app) 
      .get('/app/my_apis/darn_good_api/endpoints/any/other/endpoint ')
      .set('Accept', 'application/json')
      .expect(200)
      .end(function(err, res) {
        if (err) return done(err);
        // expect(res.body).to.be.an('array'); 
        // expect(res.body).to.be.empty; 
        done();
      })

    });

    it('should be able to write if auth valid', function(done) { 
      request(app) 
      .get('/app/my_apis/darn_good_api/endpoints/any/other/endpoint ')
      .set('Accept', 'application/json')
      .expect(200)
      .end(function(err, res) {
        if (err) return done(err);
        // expect(res.body).to.be.an('array'); 
        // expect(res.body).to.be.empty; 
        done();
      })

    });
    
  });


  describe('At /app/other_api/{other_endpoint}', function() { 

    it('should be able to GET if accepts JSON', function(done) { 
      request(app) 
      .get('/app/other_api/awesome_endpoint')
      .set('Accept', 'application/json')
      .expect(200)
      .end(function(err, res) {
        if (err) return done(err);
        // expect(res.body).to.be.an('array'); 
        // expect(res.body).to.be.empty; 
        done();
      })

    });


    describe('if has body, ', function() { 

      it('should be able to POST', function(done) { 
        request(app) 
        .get('/app/other_api/awesome_endpoint')
        .set('Accept', 'application/json')
        .expect(200)
        .end(function(err, res) {
          if (err) return done(err);
          // expect(res.body).to.be.an('array'); 
          // expect(res.body).to.be.empty; 
          done();
        })
  
      });

      it('should be able to PUT', function(done) { 
        request(app) 
        .get('/app/other_api/awesome_endpoint')
        .set('Accept', 'application/json')
        .expect(200)
        .end(function(err, res) {
          if (err) return done(err);
          // expect(res.body).to.be.an('array'); 
          // expect(res.body).to.be.empty; 
          done();
        })
  
      });

      it('should be able to DELETE', function(done) { 
        request(app) 
        .get('/app/other_api/awesome_endpoint')
        .set('Accept', 'application/json')
        .expect(200)
        .end(function(err, res) {
          if (err) return done(err);
          // expect(res.body).to.be.an('array'); 
          // expect(res.body).to.be.empty; 
          done();
        })
  
      });
      
      
    });
      

    
  });










});

// describe('Array', function() {
//   describe('#includes()', function() {
//     it('should return -1 when the value is not present', function() {
//       assert( ![1,2,3].includes(4) );
//     });
//   });
// });

