package l3

import l3.{SymbolicCL3TreeModule => S}
import l3.{HighCPSTreeModule => H}

object CL3ToCPSTranslator extends (S.Tree => H.Tree) {
  def apply(tree: S.Tree): H.Tree =
    transform(tree)(_ => H.Halt(IntLit(L3Int(0))))

  private def transform(tree : S.Tree)(ctx: H.Atom => H.Tree): H.Tree = {
    given Position = tree.pos

    tree match {
      case S.Lit(value) => 
        ctx(value)
      case S.Ident(name) =>  
        ctx(name)
    }
  }
    


}
