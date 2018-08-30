export const validVariableName = /^[a-zA-Z_$][a-zA-Z_$0-9]*$/
export const toUniformCase = m => m.toLowerCase()

// 'read only' are HTTP safe methods
export const READ_METHODS = [
    'GET', 
    'HEAD',
    'OPTIONS'
].map(toUniformCase)

// 'write' are HTTP unsafe methods
export const WRITE_METHODS = [
  'TRACE',
  'CONNECT',
  'DELETE',
  'PATCH',
  'POST',
  'PUT'
].map(toUniformCase)


// switch (ex) {
//   case 'b': return "\b";
//   case 'f': return "\f";
//   case 'n': return "\n";
//   case 'r': return "\r";
//   case 't': return "\t";
//   case '"': return "\"";
//   case '\'': return "\'";
//   case '\\': return "\\";
// }