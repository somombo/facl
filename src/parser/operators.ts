export default class Operators {
  static not(p) {
    return !p
  }
  static negative(p) {
    console.log("negative here:", p)
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
    return p[s]
  }
  static index(p,s) {
    return p[s]
  }
  static construct(p,s) {
    return new p(s)
  }
  static invoke(p,s) {
    return p(s)
  }

}