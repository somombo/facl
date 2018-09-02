{

  global["__fire$service__"] = function(name, matches){ return { class: "SERVICE", type:name, matches } }
  global["__fire$match__"] = function(route, children){ return { class: "CHILD", type: "match",  route, children} }    
  global["__fire$allow__"] = function(actions, condition){ return { class: "CHILD", type: "allow", actions, condition } }

  global["__cel$ltr__"] = function(head, tail){
    return tail.reduce( (t,h) => ({...h, primary: t}), head)
  }
}


/* 
// By Chisomo M. Sakala, Mombo Solutions

// Can parse the following so far:

service https.cloudfunctions.net {
  match /app {

    match /my_apis/{api}/endpoints {
      match /{endpoint=**} {
        allow read, write: if request.auth.uid != null;
      }
    }

    allow read: if true; 

    match /other_api/{other_endpoint} {
    
      allow get: if request.accepts("json");  
        
      allow post, put, delete: if request.body != null;  
    
    }     
  }

}

*/


// start = Service

///////////////////////////////////////////////////////////////


Service 
  = __ "service" _ type:ServiceType _ "{" __ 
      matches:Matches __ 
    "}" __ { return __fire$service__(type, matches) }

ServiceType
  = "https.cloudfunctions.net" // change to match other possibilites
   
Matches
	= __ head:Match tail:( __ m:Match __ {return m})* __ {
      	return [head, ...tail]
      }

Match
  = "match" _ route:Route _ "{" children:Children "}" {
  		return __fire$match__(route, children)
  	}

Route
  = $("/" RouteToken)+
  / "/" // For the root

RouteToken
  = RouteSegment
  / RouteParam
  / RouteMatchAll

RouteSegment
  = IDENTIFIER

RouteParam
  = "{" _ IDENTIFIER _"}"

RouteMatchAll
  = "{" _ IDENTIFIER _ "=" _ "**" _ "}"

Children
	= __ head:Child tail:( __ c:Child __ {return c})* __ {
      return [head, ...tail]
    }

Child
  = Match / Allow 


Allow
  = "allow" _ actions:Actions _ ":" _ "if" __ expr:Expression __ ";" __  {
  		return __fire$allow__(actions, expr)
  	}

Condition
  = result:("true" / "false") { 
  		return result === "true" ? _ => true : _ => false 
   	}

Actions
	= head:Action tail:( _ "," _ a:Action {return a})* {
      return [head, ...tail]
    }

Action
  = 'read'i
  / 'write'i
  / 'GET'i 
  / 'HEAD'i
  / 'OPTIONS'i
  / 'DELETE'i
  / 'PATCH'i
  / 'POST'i
  / 'PUT'i




















