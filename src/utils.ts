export const validVariableName = /^[a-zA-Z_$][a-zA-Z_$0-9]*$/
export const toUniformCase = m => m.toLowerCase()

// 'read only' are HTTP safe methods
export const READ_METHODS:string[] = [
    'get', 
    'head',
    'options'
].map(toUniformCase)

// 'write' are HTTP unsafe methods
export const WRITE_METHODS:string[] = [
  'delete',
  'patch',
  'post',
  'put'
].map(toUniformCase)


