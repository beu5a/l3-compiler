package l3

import l3.{HighCPSTreeModule as H}
import l3.{LowCPSTreeModule as L}

import l3.{L3Primitive as L3}
import l3.{CPSValuePrimitive as CPS}
import l3.{CPSTestPrimitive as CPST}
import CL3Literal._
import l3.Symbol.fresh

object CPSValueRepresenter extends (H.Tree => L.Tree) {

  def apply(tree: H.Tree): L.Tree = {
    transform(tree) // transform is for trees , rewrite is for atoms
  }

  private def transform(tree: H.Tree): L.Tree = {
    tree match {
      // Continuations
      case H.LetC(cs, e) =>
        L.LetC(
          cs.map(c => L.Cnt(c.name, c.args, transform(c.body))),
          transform(e)
        )
      case H.AppC(c, as) =>
        L.AppC(c, as.map(rewrite))
      // Functions, wrong transformation
      //case H.LetF(fs, e) =>
      //  L.LetF(
      //    fs.map(f => L.Fun(f.name, f.retC, f.args, transform(f.body))),
      //    transform(e)
      //  )
      //case H.AppF(f, retC, as) =>
      //  L.AppF(rewrite(f), retC, as.map(rewrite))

      // Functions, correct transformation
      case H.AppF(a, nc, as) =>
        val new_f = Symbol.fresh("f")
        val body = L.AppF(new_f, nc, Seq(rewrite(a))++as.map(rewrite))
        L.LetP(new_f, CPS.BlockGet, Seq(rewrite(a), 0),
          body
        )
      
      case f @ H.LetF(fs, e) =>
        closure(f)

      // Integers
      case H.LetP(n, L3.IntAdd, Seq(x, y), body) =>
        tempLetP(CPS.XOr, Seq(rewrite(x), 1)) { x1 =>
          L.LetP(n, CPS.Add, Seq(x1, rewrite(y)), apply(body))
        }
      case H.LetP(n, L3.IntSub, Seq(x, y), body) =>
        tempLetP(CPS.Sub, Seq(rewrite(x), rewrite(y))) { x1 =>
          L.LetP(n, CPS.Or, Seq(x1, 1), apply(body))
        }
      case H.LetP(n, L3.IntMul, Seq(x, y), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { b =>
          tempLetP(CPS.Sub, Seq(rewrite(x), 1)) { a =>
            tempLetP(CPS.Mul, Seq(a, b)) { t =>
              L.LetP(n, CPS.Add, Seq(t, 1), apply(body))
            }
          }
        }
      case H.LetP(n, L3.IntDiv, Seq(x, y), body) =>
        tempLetP(CPS.Sub, Seq(rewrite(x), 1)) { a =>
          tempLetP(CPS.Sub, Seq(rewrite(y), 1)) { b =>
            tempLetP(CPS.Div, Seq(a, b)) { c =>
              tempLetP(CPS.ShiftLeft, Seq(c, 1)) { d =>
                L.LetP(n, CPS.Add, Seq(d, 1), apply(body))
              }
            }
          }
        }

      case H.LetP(n, L3.IntMod, Seq(x, y), body) =>
        unboxInt(rewrite(x)) { c =>
          unboxInt(rewrite(y)) { d =>
            tempLetP(CPS.Mod, Seq(c, d)) { e =>
              boxInt(e, n) { f =>
                apply(body)
              }
            }
          }
        }

      // Bitwise operations
      case H.LetP(n, L3.IntShiftLeft, Seq(x, y), body) =>
        unboxInt(rewrite(y)) { y1 =>
          tempLetP(CPS.Sub, Seq(rewrite(x), 1)) { x1 =>
            tempLetP(CPS.ShiftLeft, Seq(x1, y1)) { t =>
              L.LetP(n, CPS.Add, Seq(t, 1), apply(body))
            }
          }
        }

      case H.LetP(n, L3.IntShiftRight, Seq(x, y), body) =>
        unboxInt(rewrite(y)) { y1 =>
          unboxInt(rewrite(x)) { x1 =>
            tempLetP(CPS.ShiftRight, Seq(x1, y1)) { t =>
              boxInt(t, n) { n =>
                apply(body)
              }
            }
          }
        }

      case H.LetP(n, L3.IntBitwiseAnd, Seq(x, y), body) =>
        L.LetP(n, CPS.And, Seq(rewrite(x), rewrite(y)), apply(body))

      case H.LetP(n, L3.IntBitwiseOr, Seq(x, y), body) =>
        L.LetP(n, CPS.Or, Seq(rewrite(x), rewrite(y)), apply(body))

      case H.LetP(n, L3.IntBitwiseXOr, Seq(x, y), body) =>
        tempLetP(CPS.XOr, Seq(rewrite(x), rewrite(y))) { t =>
          L.LetP(n, CPS.Add, Seq(t, 1), apply(body))
        }

      // Byte operations
      case H.LetP(n, L3.ByteRead, Seq(), body) =>
        tempLetP(CPS.ByteRead, Seq()) { t1 =>
          boxInt(t1, n) { _ => apply(body) }
        }

      case H.LetP(n, L3.ByteWrite, Seq(x), body) =>
        unboxInt(rewrite(x)) { x1 =>
          L.LetP(n, CPS.ByteWrite, Seq(x1), apply(body))
        }

      // Block operations
      case H.LetP(n, L3.BlockAlloc, Seq(x, y), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(x), 1)) { t1 =>
          tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { t2 =>
            L.LetP(n, CPS.BlockAlloc, Seq(t1, t2), apply(body))
          }
        }

      case H.LetP(n, L3.BlockTag, Seq(x), body) =>
        tempLetP(CPS.BlockTag, Seq(rewrite(x))) { t1 =>
          boxInt(t1, n) { _ => apply(body) }
        }

      case H.LetP(n, L3.BlockLength, Seq(x), body) =>
        tempLetP(CPS.BlockLength, Seq(rewrite(x))) { t1 =>
          boxInt(t1, n) { _ => apply(body) }
        }

      case H.LetP(n, L3.BlockGet, Seq(x, y), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { t1 =>
          L.LetP(n, CPS.BlockGet, Seq(rewrite(x), t1), apply(body))
        }

      case H.LetP(n, L3.BlockSet, Seq(x, y, z), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { t1 =>
          L.LetP(n, CPS.BlockSet, Seq(rewrite(x), t1, rewrite(z)), apply(body))
        }

      // Conversions
      case H.LetP(n, L3.IntToChar, Seq(x), body) => {
        tempLetP(CPS.ShiftLeft, Seq(rewrite(x), 2)) { t1 =>
          L.LetP(n, CPS.Add, Seq(t1, 2), apply(body))
        }
      }

      case H.LetP(n, L3.CharToInt, Seq(x), body) => {
        L.LetP(n, CPS.ShiftRight, Seq(rewrite(x), 2), apply(body))
      }

      // Id
      case H.LetP(n, L3.Id, Seq(x), body) =>
        L.LetP(n, CPS.Id, Seq(rewrite(x)), apply(body))

      // Test primitive
      case H.If(L3.IntP, Seq(x), e1, e2) => {
        tempLetP(CPS.And, Seq(rewrite(x), 1)) { t1 =>
          L.If(CPST.Eq, Seq(t1, 1), e1, e2)
        }
      }

      case H.If(L3.CharP, Seq(x), e1, e2) => {
        tempLetP(CPS.And, Seq(rewrite(x), 7)) { t1 =>
          L.If(CPST.Eq, Seq(t1, 6), e1, e2)
        }
      }

      case H.If(L3.BoolP, Seq(x), e1, e2) => {
        tempLetP(CPS.And, Seq(rewrite(x), 15)) { t1 =>
          L.If(CPST.Eq, Seq(t1, 10), e1, e2)
        }
      }

      case H.If(L3.UnitP, Seq(x), e1, e2) => {
        tempLetP(CPS.And, Seq(rewrite(x), 15)) { t1 =>
          L.If(CPST.Eq, Seq(t1, 2), e1, e2)
        }
      }

      case H.If(L3.IntLt, Seq(x, y), e1, e2) => {
        L.If(CPST.Lt, Seq(rewrite(x), rewrite(y)), e1, e2)
      }
      case H.If(L3.IntLe, Seq(x, y), e1, e2) => {
        L.If(CPST.Le, Seq(rewrite(x), rewrite(y)), e1, e2)
      }
      case H.If(L3.Eq, Seq(x, y), e1, e2) => {
        L.If(CPST.Eq, Seq(rewrite(x), rewrite(y)), e1, e2)
      }

      case H.If(L3.BlockP, Seq(x), e1, e2) => {
        tempLetP(CPS.And, Seq(rewrite(x), 3)) { t1 =>
          L.If(CPST.Eq, Seq(t1, 0), e1, e2)
        }
      }

      case H.Halt(x) => unboxInt(rewrite(x)) { x1 => L.Halt(x1) }
      case _         => throw new Exception("Not implemented yet")

    }
  }

  private def boxInt(v: L.Name, n: L.Name)(body: L.Name => L.Tree): L.Tree = {
    tempLetP(CPS.ShiftLeft, Seq(v, 1)) { t =>
      L.LetP(n, CPS.Add, Seq(t, 1), body(v))
    }
  }

  private def unboxInt(x: L.Atom)(body: L.Name => L.Tree): L.Tree = {
    tempLetP(CPS.ShiftRight, Seq(x, 1)) { x2 =>
      body(x2)
    }
  }

  private def rewrite(a: H.Atom): L.Atom = {
    // Atom = Name | Literal
    a match {
      // case n: H.Name => n
      case n: H.Name => n

      // case l: H.Literal => l
      case IntLit(v)         => (v.toInt << 1) | 1
      case CharLit(c)        => (c.toInt << 3) | 6 // 0b110
      case BooleanLit(true)  => 26 // 0b11010
      case BooleanLit(false) => 10 // 0b01011
      case UnitLit           => 2 // 0b10
    }
  }

  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Atom])(
      body: L.Name => L.Tree
  ): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetP(tempSym, p, args, body(tempSym))
  }

  private def freeVariables(tree: H.Tree): Set[H.Name] = {
    tree match {
      case H.LetP(n, _, args, body) =>
        freeVariables(body) - n ++ args.flatMap(freeAtom)
      case H.LetC(cs, body) =>
        val cntFreeVars = cs.flatMap(c => freeVariables(c.body) -- c.args).toSet
        freeVariables(body) ++ cntFreeVars
      case H.LetF(fs, body) =>
        val funFreeVars = fs.flatMap(f => freeVariables(f.body) --  f.args).toSet
        val funNames = fs.map(_.name).toSet
        freeVariables(body) ++ funFreeVars -- funNames
      case H.AppC(_, args) =>
        args.flatMap(freeAtom).toSet
      case H.AppF(fun, _, args) =>
        freeAtom(fun) ++ args.flatMap(freeAtom).toSet
      case H.If(_, args, _, _) =>
        args.flatMap(freeAtom).toSet
      case H.Halt(arg) =>
        freeAtom(arg)

  }
}

  private def freeAtom(atom: H.Atom): Set[H.Name] = {
    atom match {
      case n: H.Name => Set(n)
      case _         => Set() // put nothing in case of literals
    }
  }

  private def substitute(tree: L.Tree)(implicit s: Subst[Symbol]): L.Tree = {
    def subst(a: L.Atom): L.Atom = a match
      case n: L.Name => s.getOrElse(n, n)
      case _         => a
    tree match
      case L.LetF(funs, body) =>
        def subF(f: L.Fun): L.Fun = {
          L.Fun(f.name, f.retC, f.args, substitute(f.body))
        }
        L.LetF(funs.map(subF), substitute(body))
      case L.LetC(cnts, body) =>
        def subC(c: L.Cnt): L.Cnt = {
          L.Cnt(c.name, c.args, substitute(c.body))
        }
        L.LetC(cnts.map(subC), substitute(body))
      case L.LetP(n, prim, args, body) =>
        L.LetP(n, prim, args.map(subst), substitute(body))
      case L.AppF(fun, retC, args) =>
        L.AppF(subst(fun), s(retC), args.map(subst))
      case L.AppC(cnt, args) =>
        L.AppC(s(cnt), args.map(subst))
      case L.If(cond, args, thenC, elseC) =>
        L.If(cond, args.map(subst), s(thenC), s(elseC))
      case L.Halt(arg) =>
        L.Halt(subst(arg))
    
      
    
  }



  // SYMBOLS VS NAMES 
  private def closure(t : H.LetF) : L.Tree = {
    def blockGet(fun:Symbol, env:Symbol, fvi:Seq[(Symbol,Int)], s:Subst[Symbol], body:L.Tree):(L.Tree, Subst[Symbol]) = {
      fvi match {
        case Seq() => (substitute(body)(s),s)
        case Seq((n,i),rest@_*) => {
          val v = Symbol.fresh("v")
          val (b,nS) = blockGet(fun,env,rest,s+(n -> v),body)
          (L.LetP(v,CPS.BlockGet,Seq(env,i),substitute(b)(nS)),nS)
        }
      }
    }

    def blockSet(fun:Symbol, fvi:Seq[(Symbol,Int)], body:L.Tree):(L.Tree) = {
      fvi match {
        case Seq() => body
        case Seq((n,i),rest@_*) => {
          val t = Symbol.fresh("t")
          L.LetP(t,CPS.BlockSet,Seq(fun,i,n),blockSet(fun,rest,body)) //what about t1 , w1 
        }
      }
    }

    def closedFun(fun:H.Fun): (L.Fun, Seq[(Symbol,Int)], Symbol) = {
      val w1 = Symbol.fresh("w")
      val env1 = Symbol.fresh("env")
      val freeV = freeVariables(fun.body).toSeq
      val freeVIndex = freeV.zipWithIndex.map((n,i) => (n,i+1))
      val (funBody,s) = blockGet(fun.name, env1, freeVIndex, Map(fun.name -> env1), apply(fun.body)) 
      (L.Fun(w1,fun.retC,Seq(env1)++fun.args,funBody) , freeVIndex , w1)
    }

    def closureAlloc(f: Symbol, fvi: Seq[(Symbol,Int)])(body: L.Tree): L.Tree = {
      L.LetP(f,CPS.BlockAlloc,Seq(BlockTag.Function,fvi.size + 1),body)
    }

    def closureInit(f: Symbol, w: Symbol , fvi:  Seq[(Symbol,Int)], body: L.Tree): L.Tree ={
      val augmentedFvi = (w,0) +: fvi
      blockSet(f,augmentedFvi,body)
    }

    
    val zipped = t.funs.map(f => closedFun(f))
    val closedF = zipped.map(f => f._1)

    val e = apply(t.body)
    val initiated = zipped.foldRight(e)((f,acc) => closureInit(f._1.name, f._3, f._2, acc))
    val allocated = zipped.foldRight(initiated)((f,acc) => closureAlloc(f._1.name, f._2)(acc))
    L.LetF(closedF, allocated)
  }

 

}


  