module Types where

-- |Simple first-order types.
class Value a

instance Value Int
instance Value Integer
instance Value Bool
instance Value Double
instance (Value a, Value b) => Value (a, b)
instance (Value a) => Value [a]
