function isFunction(f){
  // TODO: Find more precise way to test for Function if there's any
    
  return typeof f === 'function'
       

}

export default class Operators {
  static not(p) {
    return !p
  }
  static negative(p) {
    return -p
  }

  ////


  static multiply(p,s) {
    return p * s
  }
  static divide(p,s) {
    return p / s
  }
  static remainder(p,s) {
    return p % s
  }
  static add(p,s) {
    return p + s
  }
  static subtract(p,s) {
    return p - s
  }
  static less(p,s) {
    return p < s
  }
  static lessOrEqual(p,s) {
    return p <= s
  }
  static greaterOrEqual(p,s) {
    return p >= s
  }
  static greater(p,s) {
    return p > s
  }
  static equal(p,s) {
    return p == s
  }
  static notEqual(p,s) {
    return p != s
  }

  static in(p,s){
    return p.has ? p.has(s) : p.includes(s)
  }
  
  static and(p,s) {
    return p + s
  }
  static or(p,s) {
    return p + s
  }
  static conditional(p,s,t) {
    return t ? s : p // it's a right-to-left op by defn
  }

  ////

  static select(p,s) {
    
     if(p[s]) return p[s] 
      
     return function(ctx){

      const P = p(ctx)
    
      return P[s] 
    
    }
  



    
  }
  static index(p,s) {
    
    return p[s] || (ctx => p(ctx)[s])
  }
  static construct(p,s) {
    try {
      return  new p(s)
      
    } finally  {
      return ctx => { 
        const P = p(ctx)
        return new P(s)
      }      
    }
    
  }
  static invoke(p,s) {

    return function(ctx) {

      const P = p(ctx)
      return P(...s)
    
    }
  }

}