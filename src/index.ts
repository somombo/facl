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
      auth: {
        uid: 1234 // TODO: REMOVE THIS Somo, for test only!
      }

    }

    for (const rule of acl) {
      
      if ( rule.isAccessibleResource(parse(req.originalUrl).pathname) ) {


        const actionAuthdAllows = rule.allows.filter( allow => /* action_matches */ allow.isAllowedAction(req.method) )

        if ( !actionAuthdAllows.length ) {
          // res.status(401).json({ error: "Unauthorized Action", status: 401, time: Date.now()})
          return next({ message: "Unauthorized Action", status: 401, time: Date.now()})
          
        }

        for (const allow of actionAuthdAllows) {

          /* get condition decision */
          if (/*  condition is met */ allow.isAllowedReqIn(context) ) {
            return next()
            
          }

        }  

        // is accessible resource, with authd action but did not meet a single auth condition
        // res.status(401).json({ error: "Access denied", status: 401, time: Date.now()})
        
        return next({ message: "Access denied", status: 401, time: Date.now()})

      }
    }

    // res.status(401).json({ error: "Not Authorized", status: 401, time: Date.now()});
    return next({ message: "Not Authorized", status: 401, time: Date.now()});

  }
}
