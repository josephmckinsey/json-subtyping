import JsonSubtyping

open JsonType

-- Basic type examples
#check (null : JsonType)
#check (bool : JsonType)
#check (number : JsonType)
#check (string : JsonType)

-- Literal types
def literalHello : JsonType := strLit "hello"
def literalFortyTwo : JsonType := numLit 42

-- Union types (like TypeScript's `string | number`)
def stringOrNumber : JsonType := string ||| number
def nullableString : JsonType := string ||| null

-- Intersection types
def bothTypes : JsonType := string &&& number  -- never in practice

-- Array types
def stringArray : JsonType := array string
def numberArray : JsonType := array number

-- Tuple types
def point2D : JsonType := tuple [number, number]
def mixedTuple : JsonType := tuple [string, number, bool]

-- Object types
def personType : JsonType := object
  [("name", string), ("age", number)]  -- required
  [("email", string)]                   -- optional

def configType : JsonType := object
  [("version", number)]
  [("debug", bool), ("logLevel", string)]

-- Complex nested types (like VegaLite ExprRef pattern)
def exprRef : JsonType := object [("expr", string)] []
def stringOrExpr : JsonType := string ||| exprRef
def numberOrExpr : JsonType := number ||| exprRef

-- Discriminated union (TypeScript-style)
def circleType : JsonType := object
  [("kind", strLit "circle"), ("radius", number)]
  []

def rectType : JsonType := object
  [("kind", strLit "rect"), ("width", number), ("height", number)]
  []

def shapeType : JsonType := circleType ||| rectType

-- Nested objects
def addressType : JsonType := object
  [("street", string), ("city", string), ("zip", string)]
  []

def companyType : JsonType := object
  [("name", string), ("address", addressType)]
  [("employees", array personType)]

#eval repr stringOrNumber
#eval repr shapeType
#eval repr companyType
