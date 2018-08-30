import { post } from 'request'
import { Request, Response, NextFunction } from 'express';

export function recaptcha(secret, headerName = 'X-MOMBO-G-RECAPTCHA-RESPONSE'){

  const url = 'https://www.google.com/recaptcha/api/siteverify';
  return (req: Request, res: Response, next: NextFunction) => {
        
    const grecaptchaResponse = req.get(headerName); /* console.log('grecaptchaResponse: ', response); */
    
    if (!grecaptchaResponse) {
      console.log('Recaptcha response is missing')
      res.json({error: 'Recaptcha response is missing'})
      return;
    }
  
    post({ url, form: {secret, response: grecaptchaResponse}, json: true }, (err, httpResponse, body) => {
      console.log({err: null, httpResponse: null, bodySuccess: body.success})
      if ( !body.success ) {
        // console.log('failed token', ++count, response.slice(-7))
        res.status(406).json(Object.assign({}, body, { mombo_error: 'Recaptcha response is invalid' }));
        return;
      }
  
      // console.log('verified token', ++count, response.slice(-7))
      next()
      return;
    })
  }
}

