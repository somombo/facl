import { Request, Response, NextFunction } from 'express';
import { parse } from 'url';

import compile from './compiler';

export default function (rules_source: string, js = false){

  const acl = compile(rules_source, js)
  const context = {}
  return (req: Request, res: Response, next: NextFunction) => {
 

    // TODO: add support for more request functionalities
    context["request"] = {

      ...req,
      accepts(str) {
        return !!req.accepts(str)
      },
      is(str) {

        return !!req.is(str)
      },
      auth: class {
        static get uid() {
          

          const auth = req.headers.authorization
          if (!auth){
            throw new Error("No auth header available")
          }
          
          const tokens = auth.split(" ")
          if (!tokens || !tokens.length) {
            throw new Error("Cannot parse auth token")
          }

          const authToken = tokens[ tokens.length - 1 ]

          return  authToken
        }
      }
      

        
    }


    for (const rule of acl) {
      
      if ( rule.isAccessibleResource(parse(req.originalUrl).pathname) ) {


        const actionAuthdAllows = rule.allows.filter( allow => /* action_matches */ allow.isAllowedAction(req.method) )

        if ( !actionAuthdAllows.length ) {
          return res.status(401).json({ message: "Unauthorized Action", status: 401, time: Date.now()})
          
        }

        for (const allow of actionAuthdAllows) {
          
          /* get condition decision */
          if (/*  condition is met */ allow.isAllowedReqIn(context) ) {
            return next()
            
          }

        }  

        // is accessible resource, with authd action but did not meet a single auth condition
        return  res.status(401).json({ message: "Access denied", status: 401, time: Date.now()})
        
      

      }
    }

    return res.status(401).json({ message: "Not Authorized", status: 401, time: Date.now()});

  }
}
