-- SUMMARY: Central registry resolving qualified prelude paths to values, types, and constructors.
import Mica.Frontend.AST
import Mica.TinyML.Types

/-!
This file is the single frontend entry point for prelude qualified paths
(`Module.foo`, `Module.Submodule.bar`).

Three independent namespaces:

* values — `Resolver.value`: paths used in expression position;
* types — `Resolver.type_`: paths used as type constructors;
* ctors — `Resolver.ctor`: paths used as data constructors.
-/

namespace Frontend

inductive ResolvedValue where
  | userVar (name : String)
  | primitive (name : String) (ty : TinyML.Typ)
  deriving Repr, Inhabited

inductive ResolvedType where
  | alias (path : Path)
  deriving Repr, Inhabited

inductive ResolvedCtor where
  | aliased (name : Constructor)
  deriving Repr, Inhabited

structure Resolver where
  values : List (Path × ResolvedValue) := []
  types  : List (Path × ResolvedType)  := []
  ctors  : List (Path × ResolvedCtor)  := []
  deriving Inhabited

def Resolver.value (r : Resolver) (p : Path) : Option ResolvedValue := List.lookup p r.values
def Resolver.type_ (r : Resolver) (p : Path) : Option ResolvedType  := List.lookup p r.types
def Resolver.ctor  (r : Resolver) (p : Path) : Option ResolvedCtor  := List.lookup p r.ctors


end Frontend
