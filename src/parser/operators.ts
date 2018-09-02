export default class self {
  static not(p) {
    return ctx => !p(ctx)
  }

  static negative(p) {
    return ctx => -p(ctx)
  }

  ////
  static multiply(p,s) {
    return ctx => p(ctx) * s(ctx)
  }

  static divide(p,s) {
    return ctx => p(ctx) / s(ctx)
  }

  static remainder(p,s) {
    return ctx => p(ctx) % s(ctx)
  }

  static add(p,s) {
    return ctx => p(ctx) + s(ctx)
  }

  static subtract(p,s) {
    return ctx => p(ctx) - s(ctx)
  }

  static less(p,s) {
    return ctx => p(ctx) < s(ctx)
  }

  static lessOrEqual(p,s) {
    return ctx => p(ctx) <= s(ctx)
  }

  static greaterOrEqual(p,s) {
    return ctx => p(ctx) >= s(ctx)
  }

  static greater(p,s) {
    return ctx => p(ctx) > s(ctx)
  }

  static equal(p,s) {
    return ctx => p(ctx) == s(ctx)
  }

  static notEqual(p,s) {
    return ctx => {

      const result = p(ctx) != s(ctx)
      
      return result
    }
  }

  static in(p,s){
    return ctx => p(ctx).has ? p(ctx).has(s) : p(ctx).includes(s)
  }
  
  static and(p,s) {
    return ctx => p(ctx) + s(ctx)
  }

  static or(p,s) {
    return ctx => p(ctx) + s(ctx)
  }

  static conditional(p,s,t) {
    return ctx => t(ctx) ? s(ctx) : p(ctx) // it's a right-to-left op by defn
  }

  ////

  static select(p,s) {
      
     return self.index(p,s) // select
    
  }

  static index(p,s) {
    

    return ctx => p(ctx)[s(ctx)] // index
  }

  static construct(p,s) {

    return ctx => new (p(ctx))(s(ctx))  
    
  }
  
  static invoke(p,s) {

    return ctx => p(ctx)(...s(ctx))
  }

}