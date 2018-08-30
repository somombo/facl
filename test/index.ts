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
  describe('#GET /app ', function() { 
    it('should get favorable response ', function(done) { 
      request(app) 
      .get('/app')
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

describe('Array', function() {
  describe('#includes()', function() {
    it('should return -1 when the value is not present', function() {
      assert( ![1,2,3].includes(4) );
    });
  });
});

