package l3

import l3.{HighCPSTreeModule as H}
import l3.{LowCPSTreeModule as L}

import l3.{L3Primitive as L3}
import l3.{CPSValuePrimitive as CPS}
import l3.{CPSTestPrimitive as CPST}
import CL3Literal._
import l3.Symbol.fresh

object CPSValueRepresenter extends (H.Tree => L.Tree) {

  type FV = Map[Symbol, Set[Symbol]]
  private var fv: FV = Map.empty
  private var knownWorkers: Map[Symbol, Symbol] = Map.empty

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

      // Functions, correct transformation
      case f @ H.LetF(fs, e) =>
        closure(f)

      case H.AppF(fun: H.Name, retC: H.Name, args: Seq[H.Atom]) =>
        // find worker function
        val hasWorker = knownWorkers.get(fun)
        hasWorker match
          case None =>
            val f = Symbol.fresh("f")
            val aFun = rewrite(fun)
            L.LetP(
              f,
              CPS.BlockGet,
              Seq(aFun, 0),
              L.AppF(f, retC, aFun +: args.map(rewrite(_)))
            )
          case Some(worker) =>
            L.AppF(worker, retC, args.map(rewrite(_)) ++ fv(fun))

      // Integers
      case H.LetP(n, L3.IntAdd, Seq(x, y), body) =>
        tempLetP(CPS.XOr, Seq(rewrite(x), 1)) { x1 =>
          L.LetP(n, CPS.Add, Seq(x1, rewrite(y)), transform(body))
        }
      case H.LetP(n, L3.IntSub, Seq(x, y), body) =>
        tempLetP(CPS.Sub, Seq(rewrite(x), rewrite(y))) { x1 =>
          L.LetP(n, CPS.Or, Seq(x1, 1), transform(body))
        }
      case H.LetP(n, L3.IntMul, Seq(x, y), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { b =>
          tempLetP(CPS.Sub, Seq(rewrite(x), 1)) { a =>
            tempLetP(CPS.Mul, Seq(a, b)) { t =>
              L.LetP(n, CPS.Add, Seq(t, 1), transform(body))
            }
          }
        }
      case H.LetP(n, L3.IntDiv, Seq(x, y), body) =>
        tempLetP(CPS.Sub, Seq(rewrite(x), 1)) { a =>
          tempLetP(CPS.Sub, Seq(rewrite(y), 1)) { b =>
            tempLetP(CPS.Div, Seq(a, b)) { c =>
              tempLetP(CPS.ShiftLeft, Seq(c, 1)) { d =>
                L.LetP(n, CPS.Add, Seq(d, 1), transform(body))
              }
            }
          }
        }

      case H.LetP(n, L3.IntMod, Seq(x, y), body) =>
        unboxInt(rewrite(x)) { c =>
          unboxInt(rewrite(y)) { d =>
            tempLetP(CPS.Mod, Seq(c, d)) { e =>
              boxInt(e, n) { f =>
                transform(body)
              }
            }
          }
        }

      // Bitwise operations
      case H.LetP(n, L3.IntShiftLeft, Seq(x, y), body) =>
        unboxInt(rewrite(y)) { y1 =>
          tempLetP(CPS.Sub, Seq(rewrite(x), 1)) { x1 =>
            tempLetP(CPS.ShiftLeft, Seq(x1, y1)) { t =>
              L.LetP(n, CPS.Add, Seq(t, 1), transform(body))
            }
          }
        }

      case H.LetP(n, L3.IntShiftRight, Seq(x, y), body) =>
        unboxInt(rewrite(y)) { y1 =>
          unboxInt(rewrite(x)) { x1 =>
            tempLetP(CPS.ShiftRight, Seq(x1, y1)) { t =>
              boxInt(t, n) { n =>
                transform(body)
              }
            }
          }
        }

      case H.LetP(n, L3.IntBitwiseAnd, Seq(x, y), body) =>
        L.LetP(n, CPS.And, Seq(rewrite(x), rewrite(y)), transform(body))

      case H.LetP(n, L3.IntBitwiseOr, Seq(x, y), body) =>
        L.LetP(n, CPS.Or, Seq(rewrite(x), rewrite(y)), transform(body))

      case H.LetP(n, L3.IntBitwiseXOr, Seq(x, y), body) =>
        tempLetP(CPS.XOr, Seq(rewrite(x), rewrite(y))) { t =>
          L.LetP(n, CPS.Add, Seq(t, 1), transform(body))
        }

      // Byte operations
      case H.LetP(n, L3.ByteRead, Seq(), body) =>
        tempLetP(CPS.ByteRead, Seq()) { t1 =>
          boxInt(t1, n) { _ => transform(body) }
        }

      case H.LetP(n, L3.ByteWrite, Seq(x), body) =>
        unboxInt(rewrite(x)) { x1 =>
          L.LetP(n, CPS.ByteWrite, Seq(x1), transform(body))
        }

      // Block operations
      case H.LetP(n, L3.BlockAlloc, Seq(x, y), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(x), 1)) { t1 =>
          tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { t2 =>
            L.LetP(n, CPS.BlockAlloc, Seq(t1, t2), transform(body))
          }
        }

      case H.LetP(n, L3.BlockTag, Seq(x), body) =>
        tempLetP(CPS.BlockTag, Seq(rewrite(x))) { t1 =>
          boxInt(t1, n) { _ => transform(body) }
        }

      case H.LetP(n, L3.BlockLength, Seq(x), body) =>
        tempLetP(CPS.BlockLength, Seq(rewrite(x))) { t1 =>
          boxInt(t1, n) { _ => transform(body) }
        }

      case H.LetP(n, L3.BlockGet, Seq(x, y), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { t1 =>
          L.LetP(n, CPS.BlockGet, Seq(rewrite(x), t1), transform(body))
        }

      case H.LetP(n, L3.BlockSet, Seq(x, y, z), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { t1 =>
          L.LetP(
            n,
            CPS.BlockSet,
            Seq(rewrite(x), t1, rewrite(z)),
            transform(body)
          )
        }

      // Conversions
      case H.LetP(n, L3.IntToChar, Seq(x), body) => {
        tempLetP(CPS.ShiftLeft, Seq(rewrite(x), 2)) { t1 =>
          L.LetP(n, CPS.Add, Seq(t1, 2), transform(body))
        }
      }

      case H.LetP(n, L3.CharToInt, Seq(x), body) => {
        L.LetP(n, CPS.ShiftRight, Seq(rewrite(x), 2), transform(body))
      }

      // Id
      case H.LetP(n, L3.Id, Seq(x), body) =>
        L.LetP(n, CPS.Id, Seq(rewrite(x)), transform(body))

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

  private def substitute(tree: L.Tree)(implicit s: Subst[Symbol]): L.Tree = {
    def subst(a: L.Atom): L.Atom = {
      a match
        case n: L.Name => s.getOrElse(n, n)
        case _         => a
    }
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
        L.AppF(subst(fun), retC, args.map(subst))
      case L.AppC(cnt, args) =>
        L.AppC(cnt, args.map(subst))
      case L.If(cond, args, thenC, elseC) =>
        L.If(cond, args.map(subst), thenC, elseC)
      case L.Halt(arg) =>
        L.Halt(subst(arg))

  }
// --------------------------------------------- Optimized Closure ------------------------------------------------------------

  private def blockGet(
      w: Symbol,
      c: Symbol,
      ni: Seq[Symbol],
      env: Symbol,
      fvNum: Int
  )(viAcc: Seq[Symbol]): L.Tree = {
    val pos = viAcc.size
    if (pos == fvNum) L.AppF(w, c, ni ++ viAcc)
    else
      val v = Symbol.fresh("v")
      val l = blockGet(w, c, ni, env, fvNum)(viAcc :+ v)
      L.LetP(v, CPS.BlockGet, Seq(env, pos + 1), l)
  }

  private def worker(f: H.Fun, w: Symbol, fvi: Set[Symbol]): L.Fun = {
    val freeV = fvi.toSeq
    val ui = freeV.map(_ => Symbol.fresh("ui"))
    val subTab =
      freeV.zip(ui).foldLeft(emptySubst[Symbol])((acc, kv) => acc + kv)
    val bodyAsTree = transform(f.body)
    val ei = substitute(bodyAsTree)(subTab)
    L.Fun(w, f.retC, f.args ++ ui, ei)
  }

  private def wrapper(fun: H.Fun, workerF: L.Fun, fvNum: Int): L.Fun = {
    val s = Symbol.fresh("s")
    val c = Symbol.fresh("c")
    val env = Symbol.fresh("env")
    val ni = fun.args.map(_ => Symbol.fresh("ni"))
    val body = blockGet(workerF.name, c, ni, env, fvNum)(Seq.empty[Symbol])
    L.Fun(s, c, env +: ni, body)
  }

  private def closure(t: H.LetF): L.Tree = {

    val funToFreeVars = stableFreeVars(t.funs)
    val funToWorkerNames = t.funs.map(f => (f.name, Symbol.fresh("w"))).toMap
    knownWorkers = knownWorkers ++ funToWorkerNames

    val (funToWorker, funToWrapper) =
      t.funs.foldLeft((Map.empty[Symbol, L.Fun], Map.empty[Symbol, L.Fun])) {
        case ((funToWorker, funToWrapper), f) =>
          val w = funToWorkerNames(f.name)
          val workerF = worker(f, w, funToFreeVars(f.name).toSet)
          val wrapperF = wrapper(f, workerF, funToFreeVars(f.name).size)
          (
            funToWorker + (f.name -> workerF),
            funToWrapper + (f.name -> wrapperF)
          )
      }

    val funToWrapperNames = funToWrapper.map(kv => (kv._1, kv._2.name))
    val wrapIterator = t.funs.map(f =>
      (f.name, funToWrapperNames(f.name), funToFreeVars(f.name).toSeq)
    )

    val initialAllocated = transform(t.body)
    val finalAllocated = wrapIterator.foldLeft(initialAllocated) {
      case (alloc, (f, s, fvs)) =>
        val fvSet = fvs.zipWithIndex.foldLeft(alloc) {
          case (acc, (fv, index)) =>
            L.LetP(Symbol.fresh("t"), CPS.BlockSet, Seq(f, index + 1, fv), acc)
        }
        val sSet = L.LetP(Symbol.fresh("t"), CPS.BlockSet, Seq(f, 0, s), fvSet)
        L.LetP(f, CPS.BlockAlloc, Seq(BlockTag.Function, fvs.size + 1), sSet)
    }

    val workerFuns = funToWorker.values.toSeq
    val wrapperFuns = funToWrapper.values.toSeq
    L.LetF(workerFuns ++ wrapperFuns, finalAllocated)
  }

//---------------------------------------------- Free Variables ------------------------------------------------------------
  private def freeVariables(tree: H.Tree, free: FV): Set[Symbol] = {
    tree match {
      case H.LetP(n, _, args, body) =>
        freeVariables(body, free) - n ++ args.flatMap(freeAtom)

      case H.LetC(cs, body) =>
        val cntFreeVars =
          cs.flatMap(c => freeVariables(c.body, free) -- c.args).toSet
        freeVariables(body, free) ++ cntFreeVars

      case H.LetF(fs, body) =>
        val stableFV = stableFreeVars(fs).values.flatten.toSet
        val funNames = fs.map(_.name).toSet
        freeVariables(body, free) ++ stableFV -- funNames

      case H.AppC(_, args) =>
        args.flatMap(freeAtom).toSet

      case H.AppF(fun, _, args) =>
        val freefun = freeAtom(fun)
        val funFreeVars = free.get(freefun.head)
        funFreeVars match
          case None      => freeAtom(fun) ++ args.flatMap(freeAtom).toSet
          case Some(fvs) => fvs ++ args.flatMap(freeAtom).toSet

      case H.If(_, args, _, _) =>
        args.flatMap(freeAtom).toSet
      case H.Halt(arg) =>
        freeAtom(arg)
    }
  }

  private def stableFreeVars(funs: Seq[H.Fun]): Map[Symbol, Set[Symbol]] = {
    def iterate(
        previous: Map[Symbol, Set[Symbol]],
        current: Map[Symbol, Set[Symbol]]
    ): Map[Symbol, Set[Symbol]] = {
      if (current == previous) {
        current
      } else {
        val next = funs.foldLeft(current) { (acc, fun) =>
          val H.Fun(f, _, as, e) = fun
          acc.updated(f, freeVariables(e, fv.toMap ++ acc) - f -- as.toSet)
        }
        iterate(current, next)
      }
    }

    val initial = funs.map(fun => (fun.name -> Set.empty[Symbol])).toMap
    val result = iterate(Map.empty[Symbol, Set[Symbol]], initial)

    fv ++= result
    result
  }

  private def freeAtom(atom: H.Atom): Set[H.Name] = {
    atom match {
      case n: H.Name => Set(n)
      case _         => Set() // put nothing in case of literals
    }
  }

// ---------------------------------------------- Helper Functions ------------------------------------------------------------
  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Atom])(
      body: L.Name => L.Tree
  ): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetP(tempSym, p, args, body(tempSym))
  }
}
