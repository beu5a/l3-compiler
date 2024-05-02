package l3

import scala.collection.mutable.{ Map => MutableMap }
import scala.reflect.TypeTest
import scala.annotation.tailrec

abstract class CPSOptimizer[T <: SymbolicNames]
  (protected val treeModule: T)
  (using TypeTest[treeModule.Atom, treeModule.Literal],
         TypeTest[treeModule.Atom, treeModule.Name],
         TypeTest[treeModule.Tree, treeModule.Body]) {
  import treeModule._

  protected def rewrite(tree: Program): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = size(simplifiedTree) * 3 / 2
    fixedPoint(simplifiedTree, 8)(`inline`(_, maxSize))
  }

  private case class Count(applied: Int = 0, asValue: Int = 0)

  private case class State(
    census: Map[Name, Count],
    aSubst: Subst[Atom] = emptySubst,
    cSubst: Subst[Name] = emptySubst,
    eInvEnv: Map[(ValuePrimitive, Seq[Atom]), Atom] = Map.empty,
    cEnv: Map[Name, Cnt] = Map.empty,
    fEnv: Map[Name, Fun] = Map.empty) {

    def dead(s: Name): Boolean =
      ! census.contains(s)
    def appliedOnce(s: Name): Boolean =
      census.get(s).contains(Count(applied = 1))

    def hasFun(fun: Name, actualArgs: Seq[Atom]): Boolean =
      fEnv.get(fun).exists(_.args.length == actualArgs.length)
    def hasCnt(cnt: Name, actualArgs: Seq[Atom]): Boolean =
      cEnv.get(cnt).exists(_.args.length == actualArgs.length)

    def withASubst(from: Atom, to: Atom): State =
      copy(aSubst = aSubst + (from -> aSubst(to)))
    def withASubst(from: Seq[Name], to: Seq[Atom]): State =
      copy(aSubst = aSubst ++ (from zip to.map(aSubst)))

    def withCSubst(from: Name, to: Name): State =
      copy(cSubst = cSubst + (from -> cSubst(to)))

    def withExp(atom: Atom, prim: ValuePrimitive, args: Seq[Atom]): State =
      copy(eInvEnv = eInvEnv + ((prim, args) -> atom))

    def withCnts(cnts: Seq[Cnt]): State =
      copy(cEnv = cEnv ++ (cnts.map(_.name) zip cnts))
    def withFuns(funs: Seq[Fun]): State =
      copy(fEnv = fEnv ++ (funs.map(_.name) zip funs))
  }

  // Needed for the construction of trees containing other trees,
  // which requires checking (dynamically here) it is indeed a subtype of Body.
  given Conversion[Tree, Body] = {
    case body: Body => body
    case other => sys.error(s"${other} is not a Body")
  }

  // Shrinking optimizations

  private def shrink(tree: Tree): Tree =
    shrink(tree, State(census(tree)))

  //Hassan: Put it on top
  import CL3Literal._
  import L3Primitive._

  private def shrinkLetP(tree: Tree, s: State): Tree = {
    tree match {
      //dead code elimination
      case LetP(name, prim, args, body) if s.dead(name) && !impure(prim) => 
        shrink(body, s)

      //neutral absorbing elim
      case LetP(name, prim,Seq(x:Literal, y), body) if leftNeutral.contains((x, prim)) => 
        shrink(body, s.withASubst(name, y))
      case LetP(name, prim, Seq(x, y:Literal), body) if rightNeutral.contains((prim, y)) => 
        shrink(body, s.withASubst(name, x))
      case LetP(name, prim, Seq(x:Literal, y), body) if leftAbsorbing.contains((x, prim)) =>
        shrink(body, s.withASubst(name, x))
      case LetP(name, prim, Seq(x, y:Literal), body) if rightAbsorbing.contains((prim, y)) =>
        shrink(body, s.withASubst(name, y))

        //identity
      case LetP(name,Id, Seq(a), body) => 
        shrink(body, s.withASubst(name, a))

      //CSE
      case LetP(name, prim, args, body) if s.eInvEnv.contains((prim, args)) && !impure(prim) && !unstable(prim) => 
        shrink(body, s.withASubst(name, s.eInvEnv((prim, args))))

      //constant folding
      case LetP(name,prim, l@ Seq(x:Literal, y:Literal), body) =>
          val res = vEvaluator(prim, l)
          shrink(body, s.withASubst(name, res))

      case LetP(name, prim, args, body) =>
        val newArgs = args map s.aSubst
        val updatedS = s.withExp(name, prim, newArgs)
        LetP(name, prim, newArgs, shrink(body, updatedS))
    }
  }

  private def shrink(tree: Tree, s: State): Tree = {
      tree match {

        case LetF(funs, body) =>
          val notDeadFuns = funs.filter(f => !s.dead(f.name))
          val (inlineFuns, remainingFuns) = notDeadFuns.partition(f =>s.appliedOnce(f.name))
          val updatedS = s.withFuns(remainingFuns)
          if (remainingFuns.isEmpty) shrink(body, updatedS)
          else
            val shrunkFuns = remainingFuns.map(f => Fun(f.name, f.retC, f.args, shrink(f.body, updatedS)))
            LetF(shrunkFuns, shrink(body, updatedS))

        case LetC(cnts, body) =>
          val notDeadCnts = cnts.filter(c => !s.dead(c.name))
          val (inlineCnts, remainingCnts) = notDeadCnts.partition(c => s.appliedOnce(c.name))
          val updatedS = s.withCnts(remainingCnts)
          if (remainingCnts.isEmpty) shrink(body, updatedS)
          else
            val shrunkCnts = remainingCnts.map(c => Cnt(c.name, c.args, shrink(c.body, updatedS)))
            LetC(shrunkCnts, shrink(body, updatedS))

        case If(cond, args @ Seq(IntLit(x),IntLit(y)), thenC, elseC) =>
          val res = cEvaluator(cond, args)
          shrink(AppC(if(res) then thenC else elseC,Seq()), s)
        case If(cond, args @ Seq(a,b), thenC, elseC) if a == b =>
          shrink(AppC(if(sameArgReduceC(cond)) then thenC else elseC, Seq()), s)
        case If(cond, Seq(v1,v2), thenC, elseC) if (sameArgReduceC(cond))  =>  { //Boolean ?
          val ev = if(v1 == v2) thenC else elseC
          shrink(AppC(ev, Seq()), s)
        }

        case LetP(name, prim, args, body) => shrinkLetP(tree, s)

        case AppC(cnt, args) =>
          s.cEnv.get(s.cSubst(cnt)) match {
            case Some(c) => shrink(c.body, s.withASubst(c.args, args))
            case None => AppC(s.cSubst(cnt), args map s.aSubst)
        }

        case AppF(fun, retC, args) if s.fEnv.contains(s.aSubst(fun).asInstanceOf[Name]) => 
          val name = s.aSubst(fun).asInstanceOf[Name]
          val f = s.fEnv(name)
          shrink(f.body, s.withASubst(f.args, args).withCSubst(f.retC, retC))

        case AppF(fun, retC, args) => 
          AppF(s.aSubst(fun), s.cSubst(retC), args map s.aSubst)


        //case Halt(arg) => ???
        case _ => tree
      }
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {
    def copyT(t: Tree, subV: Subst[Atom], subC: Subst[Name]): Tree = t match {
      case LetF(funs, body) =>
        val names = funs map (_.name)
        val names1 = names map (_.copy())
        val subV1 = subV ++ (names zip names1)
        LetF(funs map (copyF(_, subV1, subC)), copyT(body, subV1, subC))
      case LetC(cnts, body) =>
        val names = cnts map (_.name)
        val names1 = names map (_.copy())
        val subC1 = subC ++ (names zip names1)
        LetC(cnts map (copyC(_, subV, subC1)), copyT(body, subV, subC1))
      case LetP(name, prim, args, body) =>
        val name1 = name.copy()
        LetP(name1, prim, args map subV,
          copyT(body, subV + (name -> name1), subC))
      case AppF(fun, retC, args) =>
        AppF(subV(fun), subC(retC), args map subV)
      case AppC(cnt, args) =>
        AppC(subC(cnt), args map subV)
      case If(cond, args, thenC, elseC) =>
        If(cond, args map subV, subC(thenC), subC(elseC))
      case Halt(arg) =>
        Halt(subV(arg))
    }

    def copyF(fun: Fun, subV: Subst[Atom], subC: Subst[Name]): Fun = {
      val retC1 = fun.retC.copy()
      val subC1 = subC + (fun.retC -> retC1)
      val args1 = fun.args map (_.copy())
      val subV1 = subV ++ (fun.args zip args1)
      val funName1 = subV(fun.name).asInstanceOf[Name]
      Fun(funName1, retC1, args1, copyT(fun.body, subV1, subC1))
    }

    def copyC(cnt: Cnt, subV: Subst[Atom], subC: Subst[Name]): Cnt = {
      val args1 = cnt.args map (_.copy())
      val subV1 = subV ++ (cnt.args zip args1)
      Cnt(subC(cnt.name), args1, copyT(cnt.body, subV1, subC))
    }

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = LazyList.iterate((0, tree), fibonacci.length){ (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def inlineT(tree: Tree)(using s: State): Tree = {
        tree match {
          case LetP(name, prim, args, body) =>
            LetP(name, prim, args map s.aSubst, inlineT(body))

          case LetF(funs, body) => {
            val newFuns = funs map { f =>
              val newBody = inlineT(f.body)
              Fun(f.name, f.retC, f.args, newBody)
            }
            val fiteredFuns = newFuns.filter(f => size(f.body) <= funLimit)
            val newState = s.withFuns(fiteredFuns)

            LetF(fiteredFuns, inlineT(body)(using newState))
          }

          case LetC(cnts, body) => {
            val newCnts = cnts map { c =>
              val newBody = inlineT(c.body)
              Cnt(c.name, c.args, newBody)
            }
            val filteredCnts = newCnts.filter(c => size(c.body) <= cntLimit)
            val newState = s.withCnts(filteredCnts)

            LetC(filteredCnts, inlineT(body)(using newState))
          }

          case AppF(fun, retC, args)  => {
            fun match{
              case f: Name=> {
                val funS = s.fEnv.get(f)
                funS match {
                  case Some(Fun(_, ret, argsF, bodyf))  =>
                    val aS = s.aSubst ++ (argsF zip args).toMap
                    val cS = s.cSubst + (ret -> retC)
                    copyT(bodyf, aS, cS)
                  case _ => AppF(s.aSubst(fun), s.cSubst(retC), args map s.aSubst)
                }
              }
              case _ => AppF(s.aSubst(fun), s.cSubst(retC), args map s.aSubst)

            }

            //funS match {
            //  case Some(Fun(_, ret, argsF, bodyf))  =>
            //      val aS = s.aSubst ++ (argsF zip args).toMap
            //      val cS = s.cSubst + (ret -> retC)
            //      copyT(bodyf, aS, cS)
            //  case _ => AppF(s.aSubst(fun), s.cSubst(retC), args map s.aSubst)
            //}

          }

          case AppC(cnt, args) => {
            val cntS = s.cEnv.get(cnt)
            cntS match {
              case Some(Cnt(_, argsC, body)) =>
                val aS = s.aSubst ++ (argsC zip args).toMap
                copyT(body, aS, s.cSubst)
              case _ => AppC(s.cSubst(cnt), args map s.aSubst)
            }
          }
          case If(cond, args, thenC, elseC) => If(cond, args map s.aSubst, s.cSubst(thenC), s.cSubst(elseC))
          case Halt(arg) => Halt(s.aSubst(arg))
        }
      } 

      (i + 1, fixedPoint(inlineT(tree)(using State(census(tree))))(shrink))
    }

    trees.takeWhile{ (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]().withDefault(_ => Count())
    val rhs = MutableMap[Name, Tree]()

    def incAppUse(atom: Atom): Unit = atom match {
      case n: Name =>
        val currCount = census(n)
        census(n) = currCount.copy(applied = currCount.applied + 1)
        rhs.remove(n).foreach(addToCensus)
      case _: Literal =>
    }

    def incValUse(atom: Atom): Unit = atom match {
      case n: Name =>
        val currCount = census(n)
        census(n) = currCount.copy(asValue = currCount.asValue + 1)
        rhs.remove(n).foreach(addToCensus)
      case _: Literal =>
    }

    @tailrec
    def addToCensus(tree: Tree): Unit = tree match {
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetP(_, _, args, body) =>
        args foreach incValUse; addToCensus(body)
      case AppF(fun, retC, args) =>
        incAppUse(fun); incValUse(retC); args foreach incValUse
      case AppC(cnt, args) =>
        incAppUse(cnt); args foreach incValUse
      case If(_, args, thenC, elseC) =>
        args foreach incValUse; incValUse(thenC); incValUse(elseC)
      case Halt(arg) =>
        incValUse(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def size(tree: Tree): Int = tree match {
    case LetF(fs, body) => fs.map(_.body).map(size).sum + size(body)
    case LetC(cs, body) => cs.map(_.body).map(size).sum + size(body)
    case LetP(_, _, _, body) => size(body) + 1
    case _: (AppF | AppC | If | Halt) => 1
  }

  protected val impure: ValuePrimitive => Boolean
  protected val unstable: ValuePrimitive => Boolean

  protected val blockAlloc: ValuePrimitive
  protected val blockTag: ValuePrimitive
  protected val blockLength: ValuePrimitive

  protected val identity: ValuePrimitive

  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom]
  protected val sameArgReduceC: TestPrimitive => Boolean

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Atom]),
                                            Literal]
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Atom]),
                                            Boolean]
}

object HighCPSOptimizer extends CPSOptimizer(HighCPSTreeModule)
    with (HighCPSTreeModule.Program => HighCPSTreeModule.Program) {
  import treeModule._
  import CL3Literal._, L3Primitive._

  def apply(program: Program): Program =
    rewrite(program)

  private[this] given Conversion[L3Int, Literal] = IntLit.apply
  private[this] given Conversion[Int, Literal] = L3Int.apply

  protected val impure: ValuePrimitive => Boolean =
    Set(BlockSet, ByteRead, ByteWrite)

  protected val unstable: ValuePrimitive => Boolean =
    Set(BlockAlloc, BlockGet, ByteRead)

  protected val blockAlloc: ValuePrimitive = BlockAlloc
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength 

  protected val identity: ValuePrimitive = Id 

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, IntAdd), (1, IntMul), (~0, IntBitwiseAnd), (0, IntBitwiseOr), (0, IntBitwiseXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((IntAdd, 0), (IntSub, 0), (IntMul, 1), (IntDiv, 1),
        (IntShiftLeft, 0), (IntShiftRight, 0),
        (IntBitwiseAnd, ~0), (IntBitwiseOr, 0), (IntBitwiseXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, IntMul), (0, IntDiv),
        (0, IntShiftLeft), (0, IntShiftRight),
        (0, IntBitwiseAnd), (~0, IntBitwiseOr))

  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((IntMul, 0), (IntBitwiseAnd, 0), (IntBitwiseOr, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] =
    {
    case (IntBitwiseAnd | IntBitwiseOr, a) => a
    case (IntSub | IntMod | IntBitwiseXOr, _) => 0
    case (IntDiv, _) => 1
    }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] =
    case IntLe | Eq => true
    case IntLt => false

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Atom]),
                                            Literal] = 
    case (IntAdd, Seq(IntLit(x), IntLit(y) )) => x + y
    case (IntSub, Seq(IntLit(x), IntLit(y) )) => x - y
    case (IntMul, Seq(IntLit(x), IntLit(y) )) => x * y
    case (IntDiv, Seq(IntLit(x), IntLit(y) )) if y.toInt != 0 => x / y
    case (IntMod, Seq(IntLit(x), IntLit(y) )) if y.toInt != 0 => x % y

    case (IntShiftLeft,  Seq(IntLit(x), IntLit(y))) => x << y
    case (IntShiftRight, Seq(IntLit(x), IntLit(y))) => x >> y
    case (IntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => x & y
    case (IntBitwiseOr,  Seq(IntLit(x), IntLit(y))) => x | y
    case (IntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => x ^ y

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Atom]),
                                            Boolean] = 
    case (IntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (IntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (Eq, Seq(IntLit(x),IntLit(y))) => x == y
}

object FlatCPSOptimizer extends CPSOptimizer(FlatCPSTreeModule)
    with (FlatCPSTreeModule.Program => FlatCPSTreeModule.Program) {
  import treeModule._
  import CPSValuePrimitive._
  import CPSTestPrimitive._

  def apply(program: Program): Program = rewrite(program) match {
    case tree: Program => tree
    case other => LetF(Seq(), other)
  }

  protected val impure: ValuePrimitive => Boolean =
    Set(BlockSet, ByteRead, ByteWrite)

  protected val unstable: ValuePrimitive => Boolean =
    Set(BlockAlloc, BlockGet, ByteRead)

  protected val blockAlloc: ValuePrimitive = BlockAlloc
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength

  protected val identity: ValuePrimitive = Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, Add), (1, Mul), (~0, And), (0, Or), (0, XOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((Add, 0), (Sub, 0), (Mul, 1), (Div, 1),
        (ShiftLeft, 0), (ShiftRight, 0),
        (And, ~0), (Or, 0), (XOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, Mul), (0, Div),
        (0, ShiftLeft), (0, ShiftRight),
        (0, And), (~0, Or))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((Mul, 0), (And, 0), (Or, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (And | Or, a) => a
    case (Sub | Mod | XOr, _) => 0
    case (Div, _) => 1
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case Le | Eq => true
    case Lt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Atom]),
                                            Literal] = {
    case (Add, Seq(x: Literal, y: Literal)) => x + y
    case (Sub, Seq(x: Literal, y: Literal)) => x - y
    case (Mul, Seq(x: Literal, y: Literal)) => x * y
    case (Div, Seq(x: Literal, y: Literal)) if y.toInt != 0 => x / y
    case (Mod, Seq(x: Literal, y: Literal)) if y.toInt != 0 => x % y

    case (ShiftLeft,  Seq(x: Literal, y: Literal)) => x << y
    case (ShiftRight, Seq(x: Literal, y: Literal)) => x >> y
    case (And, Seq(x: Literal, y: Literal)) => x & y
    case (Or,  Seq(x: Literal, y: Literal)) => x | y
    case (XOr, Seq(x: Literal, y: Literal)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Atom]),
                                            Boolean] = {
    case (Lt, Seq(x: Literal, y: Literal)) => x < y
    case (Le, Seq(x: Literal, y: Literal)) => x <= y
    case (Eq, Seq(x: Literal, y: Literal)) => x == y
  }
}
