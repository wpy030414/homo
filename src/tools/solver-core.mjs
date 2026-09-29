// homo · 离线算法源（solver core）
// 从 homo.js §1-§6 抽取的区间 DP 值域生成、面额构造、无界分支限界与改进贪心，
// 供 tools/generate-short-table.mjs 离线物化精简表达式表使用。
// 运行时侧（homo.short.js）仅携带物化表 + 改进贪心 + 数字保持 finisher 的独立副本，
// 二者同构；行为一致性由 tools/verify.mjs 对拍保证。
//
// 相对 homo.js 原版的差异：
//   1. 分支限界去除时间/节点保险丝（离线无界，memo 保留，深度上调至 4）；
//   2. 新增改进贪心（加法边 / 上方面额减法边 / 借位变体 + 浮点 val 自检）；
//   3. parseDecimalToFraction 扩展返回未约分有效数字 m 与十进制指数 shift；
//   4. finisher 为数字保持版（无恒等折叠——块内每数字必须消耗，见研究文档 §4.4）；
//   5. 新增 printV（展示轨 AST → 求值轨函数调用式合成）与 digitBlocks（数字序列校验）。
//
// 直接运行（node tools/solver-core.mjs）执行 smoke 自检。

export const LIMIT = 2 ** 53 // IEEE-754 精确整数界限
export const BIG_LIMIT = BigInt(LIMIT)

// ==================== §1 数论工具 ====================

// 欧几里得辗转相除（Number 精确域：|a|, |b| < 2^53）
const gcdInt = (a, b) => {
  a = Math.abs(a)
  b = Math.abs(b)
  while (b) {
    const t = a % b
    a = b
    b = t
  }
  return a || 1
}

// 精确整数平方根（Math.sqrt 在 2^53 附近失真，Newton 精化兜底）
const isqrt = (n) => {
  if (n < 0) return null
  let x = Math.floor(Math.sqrt(n))
  while (x * x > n) x--
  while ((x + 1) * (x + 1) <= n) x++
  return x
}

// 防溢出安全运算：越界返回 null
// 值域证据：最终值 |p| ≤ 229028（研究文档 §2.3），未归约中间积不超过 LIMIT²，
// 故每步运算前检查即可保证全程精确
const safeMul = (a, b) =>
  Math.abs(b) === 0 ? 0 : Math.abs(a) > LIMIT / Math.abs(b) ? null : a * b
const safeAdd = (a, b) =>
  (a > 0 && b > 0 && a > LIMIT - b) || (a < 0 && b < 0 && a < -LIMIT - b)
    ? null
    : a + b

export const gcdBig = (a, b) => {
  if (a < 0n) a = -a
  if (b < 0n) b = -b
  while (b) {
    const t = a % b
    a = b
    b = t
  }
  return a || 1n
}

// ==================== §2 精确分数四则 ====================
// 值域限制在二进分数环 ℤ[1/2]（dyadic rationals）：分母为 2 的幂的分数与整数
// 在 IEEE-754 下封闭，组合全程零舍入 ⇒ 值集条目与表达式浮点求值严格一致。
// 非二进分母的中间分数一律丢弃——由此损失的"分数→整数"转换
// 由复合算子 divFloor / floorSqrt 以纯整数运算补回（见 §3）。

// 2 的幂判定：不可用位运算（JS & 将操作数截断为 32 位，q > 2^32 时误判）
const isDyadic = (q) => {
  if (q <= 0) return false
  while (q % 2 === 0) q /= 2
  return q === 1
}

// 分数规范化 + 二进性检查：非 dyadic 返回 null
const normD = (p, q) => {
  if (q < 0) {
    p = -p
    q = -q
  }
  if (!isDyadic(q)) return null
  const g = gcdInt(p, q)
  return [p / g, q / g]
}
// 仅整数的规范化（一元算子出口）
const normI = (p) => [p, 1]

const fAdd = (p1, q1, p2, q2) => {
  const d = safeMul(q1, q2)
  if (d === null) return null
  const a = safeMul(p1, q2)
  if (a === null) return null
  const b = safeMul(p2, q1)
  if (b === null) return null
  const n = safeAdd(a, b)
  if (n === null) return null
  return normD(n, d)
}
const fSub = (p1, q1, p2, q2) => fAdd(p1, q1, -p2, q2)
const fMul = (p1, q1, p2, q2) => {
  const n = safeMul(p1, p2)
  if (n === null) return null
  const d = safeMul(q1, q2)
  if (d === null) return null
  return normD(n, d)
}
// (p1/q1) ÷ (p2/q2) = (p1·q2) / (q1·p2)
const fDiv = (p1, q1, p2, q2) => (p2 === 0 ? null : fMul(p1, q1, q2, p2))

// ⌊(p1/q1) ÷ (p2/q2)⌋：纯整数实现。
// 浮点商与最近整数的距离 ≥ 1/|q1·p2|，相对舍入误差 ≤ |n|·2⁻⁵²/|d|（n 为未约分分子），
// 故 |n| < 2⁵¹ 时 floor 无歧义（安全系数 2）
const bDivFloor = (p1, q1, p2, q2) => {
  if (p2 === 0) return null
  const n = safeMul(p1, q2)
  if (n === null || Math.abs(n) > LIMIT / 4) return null
  const d = safeMul(q1, p2)
  if (d === null) return null
  const r = n % d
  const t = (n - r) / d // 截断商
  // floor 修正：非整除且商为负（分子分母异号）时 floor = trunc − 1
  return normI(r !== 0 && n < 0 !== d < 0 ? t - 1 : t)
}

// ==================== §3 一元算子 ====================

// n! 上限 18：18! ≈ 6.4e15 < 2^53 保持精确
const FACT = [1, 1]
for (let i = 2; i <= 18; i++) FACT[i] = FACT[i - 1] * i

// √ 仅保留有理结果 ⇔ 分子分母均为完全平方数（p/q 已最简）
const uFact = (p, q) => (q === 1 && p >= 0 && p <= 18 ? [FACT[p], 1] : null)
const uSqrt = (p, q) => {
  if (p < 0) return null
  const sp = isqrt(p),
    sq = isqrt(q)
  return sp * sp === p && sq * sq === q ? [sp, sq] : null
}
// ⌊p/q⌋ 的精确整数实现：JS % 为截断语义，负数须再减 1 才是 floor
const uFloor = (p, q) => {
  if (q === 1) return null
  const r = p % q
  return normI((p - r) / q - (r < 0 ? 1 : 0))
}

// ⌊√n⌋（n 非完全平方数，n > 15 才有产出意义）：浮点 √n 距最近平方数边界
// ≥ 1/(2√n) >> ulp（n ≤ 2⁵¹），floor 无歧义；非 dyadic 域的取整语义由此补回。
// 标记 aux：产物不回流组合（防值集平方爆炸），仅作最终面额。
const uFloorSqrt = (p, q) => {
  if (q !== 1 || p < 16 || p > LIMIT / 4) return null
  const s = isqrt(p)
  return s * s === p ? null : [s, 1]
}

const UNARY = [
  { f: uFact, wrap: (e) => `(${e})!`, vwrap: (e) => `F(${e})` },
  { f: uSqrt, wrap: (e) => `√(${e})`, vwrap: (e) => `SQ(${e})` },
  { f: uFloor, wrap: (e) => `⌊${e}⌋`, vwrap: (e) => `FL(${e})` },
  {
    f: uFloorSqrt,
    aux: true,
    wrap: (e) => `⌊√(${e})⌋`,
    vwrap: (e) => `FLSQ(${e})`,
  },
]

// 整数次幂。底限定整数：浮点 pow 对分数底走 exp/log 路径不保证精确；
// 整数底整数指按乘法语义精确（值 ≤ 2⁵³ 由溢出界检查保证）。
// 负指数仅 2 的幂底可保 dyadic（2⁻ᵏ）。
const bPow = (p1, q1, p2, q2) => {
  if (q2 !== 1 || Math.abs(p2) > 40 || q1 !== 1) return null
  let e = p2
  if (e === 0) return p1 === 0 ? null : [1, 1] // 0^0 语义不明，跳过
  if (p1 === 0) return e > 0 ? [0, 1] : null
  const neg = p1 < 0 && Math.abs(e) % 2 === 1 // 负指数时 e%2 为 -1，须取绝对值判奇偶
  const bp = Math.abs(p1)
  if (bp !== 1 && Math.log2(bp) * Math.abs(e) > 53) return null
  let P = 1,
    Q = 1
  const k = Math.abs(e)
  for (let i = 0; i < k; i++) {
    if (e > 0) {
      P = safeMul(P, bp)
      if (P === null) return null
    } else {
      Q = safeMul(Q, bp)
      if (Q === null) return null
    }
  }
  if (e < 0 && bp !== 1 && !isDyadic(Q)) return null
  return [neg ? -P : P, Q]
}

// ==================== §4 区间 DP 值域生成 ====================
//
// S(i,j) = 用子串 d_i..d_j 可精确表出的有理数 → 最短表达式（双轨：展示/求值）
// 双池架构：
//   core —— 四则/幂的组合结果 + 一元闭包（! √ ⌊⌋）+ 前导负。回流：作为更大
//           区间组合的操作数（完备性：任何表达式树按"一元子树落入某一侧"取分裂点）
//   aux  —— divFloor/FLSQ 复合算子产物。不回流（防值集平方爆炸），仅作最终面额
// 最终值域 = 顶层 core ∪ aux（冲突取更短表达式）。

export const buildTable = (extended, DIGITS = [1, 1, 4, 5, 1, 4]) => {
  const n = DIGITS.length
  const S = Array.from({ length: n }, () => Array(n))

  const setIfShorter = (m, k, rec) => {
    const cur = m.get(k)
    if (!cur || rec.e.length < cur.e.length) {
      m.set(k, rec)
      return !cur
    }
    return false
  }

  // 一元闭包至不动点（值域有界 ⇒ 收敛）；FLSQ 落 aux
  const close = (core, aux) => {
    const stack = [...core.keys()]
    while (stack.length) {
      const k = stack.pop()
      const { p, q, e, v } = core.get(k)
      for (const u of UNARY) {
        const r = u.f(p, q)
        if (!r) continue
        const rec = { p: r[0], q: r[1], e: u.wrap(e), v: u.vwrap(v) }
        if (u.aux) setIfShorter(aux, r[0] + "/" + r[1], rec)
        else if (setIfShorter(core, r[0] + "/" + r[1], rec))
          stack.push(r[0] + "/" + r[1])
      }
    }
  }

  // 前导负：仅 core 正整数，产物回流 core（作操作数），不回流一元闭包（防链爆炸）
  const closeNeg = (core) => {
    for (const rec of [...core.values()]) {
      if (rec.q === 1 && rec.p > 0)
        setIfShorter(core, -rec.p + "/1", {
          p: -rec.p,
          q: 1,
          e: `-(${rec.e})`,
          v: `-(${rec.v})`,
        })
    }
  }

  const combine = (core, aux, A, B) => {
    for (const a of A.core.values())
      for (const b of B.core.values()) {
        let r = fAdd(a.p, a.q, b.p, b.q)
        if (r)
          setIfShorter(core, r[0] + "/" + r[1], {
            p: r[0],
            q: r[1],
            e: `(${a.e})+(${b.e})`,
            v: `(${a.v})+(${b.v})`,
          })
        r = fSub(a.p, a.q, b.p, b.q)
        if (r)
          setIfShorter(core, r[0] + "/" + r[1], {
            p: r[0],
            q: r[1],
            e: `(${a.e})-(${b.e})`,
            v: `(${a.v})-(${b.v})`,
          })
        r = fMul(a.p, a.q, b.p, b.q)
        if (r)
          setIfShorter(core, r[0] + "/" + r[1], {
            p: r[0],
            q: r[1],
            e: `(${a.e})*(${b.e})`,
            v: `(${a.v})*(${b.v})`,
          })
        r = fDiv(a.p, a.q, b.p, b.q)
        if (r)
          setIfShorter(core, r[0] + "/" + r[1], {
            p: r[0],
            q: r[1],
            e: `(${a.e})/(${b.e})`,
            v: `(${a.v})/(${b.v})`,
          })
        r = bDivFloor(a.p, a.q, b.p, b.q)
        if (r)
          setIfShorter(aux, r[0] + "/" + r[1], {
            p: r[0],
            q: r[1],
            e: `⌊(${a.e})/(${b.e})⌋`,
            v: `FL((${a.v})/(${b.v}))`,
          })
        if (extended) {
          r = bPow(a.p, a.q, b.p, b.q)
          if (r)
            setIfShorter(core, r[0] + "/" + r[1], {
              p: r[0],
              q: r[1],
              e: `(${a.e})^(${b.e})`,
              v: `POW(${a.v},${b.v})`,
            })
        }
      }
  }

  for (let i = 0; i < n; i++) {
    const core = new Map(),
      aux = new Map()
    const lit = DIGITS[i]
    core.set(lit + "/1", { p: lit, q: 1, e: String(lit), v: String(lit) })
    if (extended) close(core, aux)
    closeNeg(core)
    S[i][i] = { core, aux }
  }
  for (let len = 2; len <= n; len++) {
    for (let i = 0, j = i + len - 1; j < n; i++, j = i + len - 1) {
      const core = new Map(),
        aux = new Map()
      const cat = Number(DIGITS.slice(i, j + 1).join(""))
      core.set(cat + "/1", { p: cat, q: 1, e: String(cat), v: String(cat) })
      if (extended) close(core, aux)
      for (let k = i; k < j; k++) combine(core, aux, S[i][k], S[k + 1][j])
      if (extended) close(core, aux)
      closeNeg(core)
      S[i][j] = { core, aux }
    }
  }
  // 合并顶层双池：冲突取更短表达式
  const { core, aux } = S[0][n - 1]
  const full = new Map(aux)
  for (const [k, rec] of core)
    if (!full.has(k) || rec.e.length < full.get(k).e.length) full.set(k, rec)
  return full
}

// ==================== §5 面额构造 ====================
// 单块非负整数（q=1，0 ≤ p ≤ 2^53）按最短展示表达式选优。
// 注：多块乘积面额（top-24 大值两两/配小值）在扩展值域下零新增——
// top-24 全部 > 2^52，乘积必溢出 2^53 界（实测验证），故不再构造。

export const buildDenoms = (table) => {
  const best = new Map()
  for (const { p, q, e } of table.values()) {
    if (q !== 1 || p < 0 || p > LIMIT) continue
    const cur = best.get(p)
    if (!cur || e.length < cur.e.length) best.set(p, e)
  }
  const vals = [...best.keys()].sort((a, b) => a - b)
  const exprs = vals.map((v) => best.get(v))
  return {
    vals,
    exprs,
    byVal: new Map(
      vals.map((v, i) => [BigInt(v), { val: BigInt(v), e: exprs[i], idx: i }]),
    ),
  }
}

// ==================== §6 输入语义（十进制解析） ====================
// String(number) 给出最短 round-trip 十进制表示，尊重用户输入意图（0.1 → 1/10 而非其二进制精确值）。
// 扩展返回：m = 未约分有效数字（无符号），shift = 十进制指数（num = ±m × 10^shift），
// p/q = 最简分数（BigInt）。m 与 shift 供极小小数的科学计数法发射使用（homo.short.js §D）。

export const parseDecimalInfo = (num) => {
  const m = /^(-?)(\d+)(?:\.(\d+))?(?:[eE]([+-]?\d+))?$/.exec(String(num))
  if (!m) return null
  const [, sign, ip, fp = "", ex = "0"] = m
  const shift = Number(ex) - fp.length
  const digits = BigInt(ip + fp)
  let p = digits,
    q = 1n
  if (shift >= 0) p *= 10n ** BigInt(shift)
  else q = 10n ** BigInt(-shift)
  if (sign === "-") p = -p
  const g = gcdBig(p, q)
  return { p: p / g, q: q / g, m: digits, shift, neg: sign === "-" }
}

// ==================== §7 AST finisher（数字保持版） ====================
// 解析 → 按优先级上下文打印最少括号。无任何恒等折叠：
// 块内每个数字必须消耗，×1 / 1^x 类"恒等式"恰是子区间数字消耗的合法（常常唯一）方式，
// 任何删除操作数的化简都会破坏 114514 数字序列约束（研究文档 §4.4）。
// printV：同一 AST 合成求值轨（函数调用式），⌊√(X)⌋ 特判为 FLSQ——
// 容差 SQ 不得进入 floor（研究文档 §8.6）。

const tokenize = (s) => {
  const toks = []
  for (let i = 0; i < s.length; ) {
    const c = s[i]
    if (c >= "0" && c <= "9") {
      let j = i
      while (j < s.length && s[j] >= "0" && s[j] <= "9") j++
      toks.push({ t: "num", v: s.slice(i, j) })
      i = j
    } else if ("+-*/^()!".includes(c) || c === "√" || c === "⌊" || c === "⌋") {
      toks.push({ t: c })
      i++
    } else if (c === " ") i++
    else throw new Error("bad token: " + c)
  }
  return toks
}

// 递归下降解析（优先级：+ − < * / < ^（右结合）< 一元负 < 后缀 ! < √ ⌊⌋ 原子）
let _toks, _pos
const parseExpr = () => {
  let l = parseTerm()
  while (_toks[_pos] && (_toks[_pos].t === "+" || _toks[_pos].t === "-"))
    l = { t: "bin", op: _toks[_pos++].t, l, r: parseTerm() }
  return l
}
const parseTerm = () => {
  let l = parsePow()
  while (_toks[_pos] && (_toks[_pos].t === "*" || _toks[_pos].t === "/"))
    l = { t: "bin", op: _toks[_pos++].t, l, r: parsePow() }
  return l
}
// 幂：右结合（指数递归取幂层级，可含前导负）
const parsePow = () => {
  const b = parseUnary()
  if (_toks[_pos] && _toks[_pos].t === "^") {
    _pos++
    return { t: "bin", op: "^", l: b, r: parsePow() }
  }
  return b
}
const parseUnary = () =>
  _toks[_pos] && _toks[_pos].t === "-"
    ? (_pos++, { t: "neg", x: parseUnary() })
    : parsePostfix()
const parsePostfix = () => {
  let x = parsePrimary()
  while (_toks[_pos] && _toks[_pos].t === "!") {
    _pos++
    x = { t: "fac", x }
  }
  return x
}
const parsePrimary = () => {
  const p = _toks[_pos]
  if (!p) throw new Error("unexpected end")
  if (p.t === "num") {
    _pos++
    return { t: "num", v: p.v }
  }
  if (p.t === "(") {
    _pos++
    const e = parseExpr()
    if (!_toks[_pos] || _toks[_pos++].t !== ")") throw new Error("expect )")
    return e
  }
  if (p.t === "√") {
    _pos++
    if (!_toks[_pos] || _toks[_pos++].t !== "(")
      throw new Error("expect ( after √")
    const e = parseExpr()
    if (!_toks[_pos] || _toks[_pos++].t !== ")") throw new Error("expect )")
    return { t: "sqrt", x: e }
  }
  if (p.t === "⌊") {
    _pos++
    const e = parseExpr()
    if (!_toks[_pos] || _toks[_pos++].t !== "⌋") throw new Error("expect ⌋")
    return { t: "floor", x: e }
  }
  throw new Error("unexpected " + p.t)
}
export const parseAst = (s) => {
  _toks = tokenize(s)
  _pos = 0
  const ast = parseExpr()
  if (_pos !== _toks.length) throw new Error("trailing tokens")
  return ast
}

// 优先级：+ − = 1，* / = 2，一元负 = 0.5（非加法左操作数位置一律加括号），
// ^ = 3，! / √ / ⌊⌋ / 数字 = 4（原子）
const pr = (n) =>
  n.t === "bin"
    ? n.op === "+" || n.op === "-"
      ? 1
      : n.op === "^"
        ? 3
        : 2
    : n.t === "neg"
      ? 0.5
      : 4

const print = (n) => {
  switch (n.t) {
    case "num":
      return n.v
    // 一元负：操作数原子则裸，否则括号；作父操作数时的隔离由父节点决定
    case "neg":
      return "-" + (pr(n.x) === 4 ? print(n.x) : `(${print(n.x)})`)
    case "fac":
      return (
        (n.x.t === "num" || n.x.t === "fac" ? print(n.x) : `(${print(n.x)})`) +
        "!"
      )
    case "sqrt":
      return `√(${print(n.x)})`
    case "floor":
      return `⌊${print(n.x)}⌋`
    case "bin": {
      // 左结合（^ 右结合）：左裸需 pr ≥ 父（^ 严格大于），右裸需 pr > 父（^ ≥）
      const p = pr(n)
      const needL = n.op === "^" ? pr(n.l) <= p : pr(n.l) < p
      const needR = n.op === "^" ? pr(n.r) < p : pr(n.r) <= p
      // neg 作左操作数：分配律下 + − * / 均值同，仅 ^ 底必须括号；
      // 作右操作数：恒括号（防 a--b，且 a+-b / a*-b 难读）
      const lParen = n.l.t === "neg" ? n.op === "^" : needL
      const rParen = n.r.t === "neg" ? true : needR
      return (
        (lParen ? `(${print(n.l)})` : print(n.l)) +
        n.op +
        (rParen ? `(${print(n.r)})` : print(n.r))
      )
    }
  }
}

export const finisher = (expr) => {
  try {
    return print(parseAst(expr))
  } catch (_) {
    return expr // 解析失败原样返回
  }
}

// 求值轨合成：函数调用式的运算符优先级与展示轨同构（函数调用视为原子 pr=4），
// 故括号判定复用 print 的规则；^ → POW(L,R)（参数为完整子表达式）；
// ⌊√(X)⌋（AST: floor(sqrt(x))）特判 FLSQ(X)——容差 SQ 不得进 floor。
const pvBin = (n) => {
  const p = pr(n)
  const needL = n.op === "^" ? pr(n.l) <= p : pr(n.l) < p
  const needR = n.op === "^" ? pr(n.r) < p : pr(n.r) <= p
  const lParen = n.l.t === "neg" ? n.op === "^" : needL
  const rParen = n.r.t === "neg" ? true : needR
  return (
    (lParen ? `(${printV(n.l)})` : printV(n.l)) +
    n.op +
    (rParen ? `(${printV(n.r)})` : printV(n.r))
  )
}
export const printV = (n) => {
  switch (n.t) {
    case "num":
      return n.v
    // 一元负：原子操作数裸出（如次正规指数 -1074），否则括号——与 print 同构
    case "neg":
      return "-" + (pr(n.x) === 4 ? printV(n.x) : `(${printV(n.x)})`)
    case "fac":
      return `F(${printV(n.x)})`
    case "sqrt":
      return `SQ(${printV(n.x)})`
    case "floor":
      return n.x.t === "sqrt" ? `FLSQ(${printV(n.x.x)})` : `FL(${printV(n.x)})`
    case "bin": {
      if (n.op === "^") return `POW(${printV(n.l)},${printV(n.r)})`
      return pvBin(n)
    }
  }
}

// ==================== §8 数字序列校验 ====================
// 提取表达式全部数字 run 按序连接，须恰为 '114514' 的 k 次重复（k ≥ 1）。
// 例外白名单：极小小数发射的科学计数后缀——v 轨 `*POW(10,E)` / `*POW(2,-1074)`、
// e 轨 `*(10)^(E)` / `*(2)^(-1074)`——其中的底数与指数字面量不属于块内数字。
// 返回块数 k；不合法返回 -1。

export const digitBlocks = (s) => {
  if (typeof s !== "string" || !s) return -1
  let t = s
    .replace(/\*POW\((?:10|2),-?\d+\)/g, "") // v 轨白名单
    .replace(/\*(?:\((?:10|2)\)|10|2)\^\(-?\d+\)/g, "") // e 轨白名单（10 可带可不带括号——print 会规范化）
    .replace(/[*\/]\((?:10|2)\)\^\(-?\d+\)/g, "") // legacy 除法形式 /(10)^(n)
  // 剥负号外包层：-(EXPR) / -(EXPR)! 等（块组合的合法外层）
  t = t.replace(/^-?\((.*)\)$/, "$1")
  const joined = (t.match(/\d+/g) || []).join("")
  return /^(114514)*$/.test(joined) ? joined.length / 6 : -1
}

// ==================== §9 官方 eval 环境（与 README 一致） ====================

export const F = (n) => {
  if (n < 0 || n !== Math.floor(n) || n > 170) throw new Error("bad !: " + n)
  let r = 1
  for (let i = 2; i <= n; i++) r *= i
  return r
}
export const SQ = (x) => {
  if (x < 0) throw new Error("bad √")
  const r = Math.sqrt(x),
    rr = Math.round(r)
  // 容差：精确有理 √(p/q) 的浮点链路（如 44^-2 ≠ 精确 1/1936）可能差 1ulp
  return Math.abs(r - rr) <= 1e-9 * Math.max(1, Math.abs(rr)) ? rr : r
}
export const FL = Math.floor
export const POW = (a, b) => a ** b
// FLSQ 无容差：语义是 floor(sqrt(x))，不能用容差 SQ（会把平方数边界值错误圆整）
export const FLSQ = (x) => Math.floor(Math.sqrt(x))
export const evalStr = (s) =>
  new Function("F", "SQ", "FL", "POW", "FLSQ", `"use strict";return (${s});`)(
    F,
    SQ,
    FL,
    POW,
    FLSQ,
  )
export const relClose = (a, b) =>
  a === b ||
  Math.abs(a - b) <= 1e-12 * Math.max(Math.abs(a), Math.abs(b), 1e-300)

// ==================== §10 改进贪心（与 homo.short.js 运行时同构） ====================
// 候选边（全部局部 O(1) 算术，无搜索、无 memo、无期限）：
//   ① 整除     D*(Q)            c = 1+c(Q)
//   ② q==1     D+(R)            c = 1+c(R)    —— 替代 D*(1)+(R)：×1 恒等块本靠
//        （已禁止的）输出端折叠消除，现在直接以加法组合，块数同、表达式更短
//   ③ 带余     D*(Q)+(R)        c = 1+c(Q)+c(R)
//   ④ 借位     D*(Q+1)-(d-r)    c = 1+c(Q+1)+c(d-r)   余数过半时
//   ⑤ 减法边   V-(V-n)          c = 1+c(V-n)   上方最近面额 V < 2n 时（2^53-1 型）
// 取 (c, e 长度) 字典序最小；浮点 val 与运算模板同序跟踪——
// ≤2^53 的目标以 val === Number(nn) 自检，不过检的候选弃选（借位边 d·(q+1) 可超
// 2^53 产生舍入，①②③⑤ 在该域内结构性精确，故总有候选可用）。
// 终止性：所有递归子值严格 < nn。

export const makeGreedy = (tab) => {
  // tab: { vals: Number[]（升序）, exprs: string[]（平行）, ov: Map<Number, string> }
  const { vals, exprs, ov } = tab
  const bisect = (nn) => {
    const key = nn > BIG_LIMIT ? Infinity : Number(nn)
    let lo = 0,
      hi = vals.length - 1,
      r = -1
    while (lo <= hi) {
      const mid = (lo + hi) >> 1
      if (vals[mid] <= key) {
        r = mid
        lo = mid + 1
      } else hi = mid - 1
    }
    return r
  }
  const greedy = (nn) => {
    // 0. override / 面额直接命中（表条目已最小化，原样返回）
    if (nn <= BIG_LIMIT) {
      const nnum = Number(nn)
      const o = ov.get(nnum)
      if (o !== undefined)
        return {
          e: o,
          len: o.length,
          c: (o.match(/\d/g) || []).length / 6,
          val: nnum,
        }
      const i = bisect(nn)
      if (i >= 0 && vals[i] === nnum)
        return { e: exprs[i], len: exprs[i].length, c: 1, val: nnum }
    }
    const target = nn <= BIG_LIMIT ? Number(nn) : null // 自检目标（>2^53 尽力语义）

    let best = null
    const consider = (cand) => {
      if (target !== null && cand.val !== target) return // 浮点自检
      if (
        !best ||
        cand.c < best.c ||
        (cand.c === best.c && cand.len < best.len)
      )
        best = cand
    }
    const mulSafe = (s) => (/[+\-]/.test(s) ? `(${s})` : s)

    const idx = bisect(nn)
    // 面额减法边 ⑤：上方最近面额 V（vals[idx+1] > nn），V < 2n 时 V-(V-n)
    // （仅 nn < 2^53 有意义：V ≤ 2^53，nn ≥ 2^53 时不存在上方面额或差非正）
    if (nn < BIG_LIMIT && idx + 1 < vals.length) {
      const V = vals[idx + 1]
      if (V > 1 && V < 2 * Number(nn)) {
        const d = BigInt(V) - nn
        if (d > 0n && d < nn) {
          const s = greedy(d)
          consider({
            c: 1 + s.c,
            len: exprs[idx + 1].length + s.len + 3,
            e: `${exprs[idx + 1]}-(${s.e})`,
            val: V - s.val,
          })
        }
      }
    }
    // 乘法/加法/借位边 ①②③④：d = ≤nn 的最大面额（>1）
    if (idx >= 0 && vals[idx] > 1) {
      const d = BigInt(vals[idx])
      const de = exprs[idx],
        dv = vals[idx],
        deLen = de.length
      const q = nn / d,
        r = nn % d
      if (q >= 1n) {
        if (r === 0n) {
          // ① 整除
          const s = greedy(q)
          consider({
            c: 1 + s.c,
            len: deLen + s.len + 1,
            e: `${mulSafe(de)}*${mulSafe(s.e)}`,
            val: dv * s.val,
          })
        } else {
          if (q === 1n) {
            // ② 加法边：D+(R)
            const s = greedy(r)
            consider({
              c: 1 + s.c,
              len: deLen + s.len + 2,
              e: `${mulSafe(de)}+(${s.e})`,
              val: dv + s.val,
            })
          } else {
            // ③ 带余
            const s1 = greedy(q),
              s2 = greedy(r)
            consider({
              c: 1 + s1.c + s2.c,
              len: deLen + s1.len + s2.len + 2,
              e: `${mulSafe(de)}*${mulSafe(s1.e)}+(${s2.e})`,
              val: dv * s1.val + s2.val,
            })
          }
          // ④ 借位：D*(Q+1)-(d-r)
          if (r * 2n > d && q + 1n < d) {
            const sQ = greedy(q + 1n),
              sB = greedy(d - r)
            consider({
              c: 1 + sQ.c + sB.c,
              len: deLen + sQ.len + sB.len + 2,
              e: `${mulSafe(de)}*${mulSafe(sQ.e)}-(${sB.e})`,
              val: dv * sQ.val - sB.val,
            })
          }
        }
      }
    }
    if (best) return best
    // 兜底：理论上不可达（①③ 结构性精确恒过检）；防御性返回 1 的表示
    const oneIdx = vals.indexOf(1)
    return {
      e: exprs[oneIdx >= 0 ? oneIdx : 0],
      len: exprs[oneIdx >= 0 ? oneIdx : 0].length,
      c: 1,
      val: 1,
    }
  }
  return greedy
}

// ==================== §11 无界分支限界（离线最优求解） ====================
// 与 homo.js 原 §5 同构，但去除时间/节点保险丝（离线可任意耗时），深度上调至 4。
// 图模型：节点 = 非负整数（BigInt）；最小化 (块数, 表达式长度) 字典序。
//   乘法边 n = d·q + r（面额降序 ⇒ q 递增 ⇒ 下界单调转劣，可提前终止）
//   借位边 n = d·(q+1) − (d−r)
//   加减边 n = v ± m（自二分定位点双侧指针按 |n−v| 升序全扫，深度受限）
// 贪心解为初始上界；块数下界 lb(m) = 1 + ⌈log_{maxVal} m⌉ 剪枝。

export const makeOptimal = (denoms) => {
  // denoms: buildDenoms 的产物（全量面额）
  const { vals, exprs } = denoms
  const N = vals.length
  const maxVal = BigInt(vals[N - 1])
  const logMax = Math.max(1, Math.log2(Number(maxVal) || 2))
  const lb = (m) => {
    if (m === 0n) return 0
    if (m <= maxVal) return 1
    const L = Math.log2(Number(m))
    return 1 + Math.ceil(L / logMax)
  }
  const byVal = denoms.byVal
  const bisect = (nn) => {
    const key = nn > BIG_LIMIT ? Infinity : Number(nn)
    let lo = 0,
      hi = N - 1,
      r = -1
    while (lo <= hi) {
      const mid = (lo + hi) >> 1
      if (vals[mid] <= key) {
        r = mid
        lo = mid + 1
      } else hi = mid - 1
    }
    return r
  }
  const mulSafe = (s) => (/[+\-]/.test(s) ? `(${s})` : s)

  // 贪心（B&B 的上界与兜底）——复用 §10 实现
  const greedy = makeGreedy({ vals, exprs, ov: new Map() })

  const memo = new Map()
  const solveRec = (nn, depth) => {
    const hitM = memo.get(nn)
    if (hitM) return hitM
    const hit = byVal.get(nn)
    if (hit) {
      const r = { c: 1, len: hit.e.length, e: hit.e }
      memo.set(nn, r)
      return r
    }

    let bestR = greedy(nn) // 初始上界
    const ubC = () => bestR.c
    const consider = (cand) => {
      if (
        cand &&
        (cand.c < bestR.c || (cand.c === bestR.c && cand.len < bestR.len))
      )
        bestR = cand
    }

    // 乘法边：面额降序扫描（vals 升序 ⇒ 倒序）
    for (let i = N - 1; i >= 0; i--) {
      const d = BigInt(vals[i])
      if (d <= 1n) break
      if (d > nn) continue
      const q = nn / d,
        r = nn % d
      if (q < 1n) continue
      // 保守提前终止：仅当 1+lb(q) ≥ 上界（后续 d 更小 ⇒ q 更大 ⇒ lb(q) 单调不减；
      // r 项无单调性，不纳入 break 条件）
      if (1 + lb(q) >= ubC()) break
      if (1 + lb(q) + (r === 0n ? 0 : lb(r)) >= ubC()) continue
      const de = exprs[i]
      const s1 = solveRec(q, depth)
      if (r === 0n) {
        consider({
          c: 1 + s1.c,
          len: de.length + s1.len + 1,
          e: `${mulSafe(de)}*${mulSafe(s1.e)}`,
        })
      } else {
        const s2 = solveRec(r, depth)
        consider({
          c: 1 + s1.c + s2.c,
          len: de.length + s1.len + s2.len + 2,
          e: `${mulSafe(de)}*${mulSafe(s1.e)}+(${s2.e})`,
        })
        if (r * 2n > d && q + 1n < d) {
          // 借位
          const sQ = solveRec(q + 1n, depth),
            sB = solveRec(d - r, depth)
          consider({
            c: 1 + sQ.c + sB.c,
            len: de.length + sQ.len + sB.len + 2,
            e: `${mulSafe(de)}*${mulSafe(sQ.e)}-(${sB.e})`,
          })
        }
      }
    }

    // 加减边：自 idx 起双侧指针按 |n−x| 升序全扫（覆盖"半值面额"如 114514+114514）；
    // |n−x| 单调不减 ⇒ 块数下界单调不减 ⇒ 满足剪枝即可终止
    if (depth > 0) {
      const idx = bisect(nn)
      let li = idx,
        ri = idx + 1
      while (li >= 0 || ri < N) {
        let i
        if (li < 0) i = ri++
        else if (ri >= N) i = li--
        else i = nn - BigInt(vals[li]) <= BigInt(vals[ri]) - nn ? li-- : ri++
        const vBig = BigInt(vals[i])
        if (vBig <= 0n || vBig === nn) continue
        const diff = vBig > nn ? vBig - nn : nn - vBig
        if (1 + lb(diff) >= ubC()) break // |n−x| 单调不减 ⇒ 下界单调
        const sub = solveRec(diff, depth - 1)
        const xe = exprs[i]
        const head = vBig > nn ? `${xe}-(${sub.e})` : `${xe}+(${sub.e})`
        consider({ c: 1 + sub.c, len: xe.length + sub.len + 3, e: head })
      }
    }

    memo.set(nn, bestR)
    return bestR
  }
  return (nn) => solveRec(nn, 4)
}

// ==================== smoke 自检（node tools/solver-core.mjs） ====================

if (
  import.meta.url === `file://${process.argv[1].replace(/\\/g, "/")}` ||
  process.argv[1].endsWith("solver-core.mjs")
) {
  let pass = 0,
    fail = 0
  const check = (ok, msg, detail) => {
    if (ok) pass++
    else {
      fail++
      console.error("  ✗ " + msg + (detail ? " :: " + detail : ""))
    }
  }

  console.log("[smoke] solver-core")

  // 1. 建表
  const t0 = Date.now()
  const table = buildTable(true)
  const buildMs = Date.now() - t0
  console.log(
    `  扩展值集: ${table.size.toLocaleString("en-US")} 条, 构建 ${buildMs}ms`,
  )
  check(table.size > 100000, "扩展值集规模", String(table.size))

  // 2. 面额统计
  const denoms = buildDenoms(table)
  const { vals, exprs } = denoms
  let cover = 0
  while (cover < vals.length && vals[cover] === cover) cover++
  console.log(`  面额: ${vals.length} 条, 连续覆盖 0..${cover - 1}`)
  check(vals.length > 40000, "面额规模", String(vals.length))

  // 3. finisher 数字保持 + printV 求值对拍（面额全量）
  let badD = 0,
    badE = 0
  for (let i = 0; i < vals.length; i++) {
    const e = finisher(exprs[i])
    if (digitBlocks(e) !== 1) {
      badD++
      if (badD <= 3) console.error(`  ✗ 数字序列 ${vals[i]}: ${e}`)
    }
    try {
      const v = printV(parseAst(e))
      const ev = evalStr(v)
      if (ev !== vals[i]) {
        badE++
        if (badE <= 3) console.error(`  ✗ printV 求值 ${vals[i]} → ${ev}: ${v}`)
      }
    } catch (err) {
      badE++
      console.error(`  ✗ printV 异常 ${vals[i]}: ${err.message}`)
    }
  }
  check(badD === 0, `面额 ${vals.length} 条 finisher 数字保持`)
  check(badE === 0, `面额 ${vals.length} 条 printV 全量求值对拍`)
  console.log(`  finisher+printV: 数字违例 ${badD}, 求值违例 ${badE}`)

  // 4. 改进贪心质量（全量面额表）
  const greedy = makeGreedy({ vals, exprs, ov: new Map() })
  let sum = 0,
    n1 = 0
  for (let n = 1; n <= 100000; n += 199) {
    sum += greedy(BigInt(n)).c
    n1++
  }
  console.log(
    `  改进贪心 [1,1e5] 采样 ${n1}: 平均块数 ${(sum / n1).toFixed(2)}`,
  )
  check(sum / n1 < 3, "贪心平均块数 < 3", (sum / n1).toFixed(2))
  const r53 = greedy(9007199254740991n)
  console.log(`  2^53-1: ${r53.c} 块`)
  check(r53.c <= 2, "2^53-1 ≤ 2 块", String(r53.c))
  check(
    evalStr(printV(parseAst(finisher(r53.e)))) === 9007199254740991,
    "2^53-1 求值精确",
  )

  // 5. 无界 B&B vs 贪心 对拍（[cover, 65536) 抽样）
  const optimal = makeOptimal(denoms)
  let worse = 0,
    checked = 0
  for (let n = cover; n < 65536; n += 7) {
    const g = greedy(BigInt(n)).c
    const o = optimal(BigInt(n)).c
    checked++
    if (o < g) {
      worse++
      if (worse <= 3) console.log(`    B&B 更优: ${n} 贪心 ${g} vs 最优 ${o}`)
    }
  }
  console.log(`  B&B 对拍 ${checked} 个: 贪心非最优 ${worse}`)
  check(true, "B&B 对拍完成（信息性）")

  // 6. parseDecimalInfo 案例
  const pd = (x) => parseDecimalInfo(x)
  check(
    pd(1e-309).m === 1n &&
      pd(1e-309).shift === -309 &&
      pd(1e-309).q > BIG_LIMIT,
    "1e-309 解析",
  )
  check(pd(0.1).p === 1n && pd(0.1).q === 10n, "0.1 → 1/10")
  check(
    pd(Number.MIN_VALUE).m === 5n && pd(Number.MIN_VALUE).shift === -324,
    "MIN_VALUE 解析",
  )
  check(pd(1e-15).q === 10n ** 15n, "1e-15 q = 10^15")

  // 7. digitBlocks 校验器自身
  check(digitBlocks("(1-1)*4514") === 1, "digitBlocks 基本形态")
  check(digitBlocks("14+(5-14)") === -1, "digitBlocks 拒绝不完整序列")
  check(
    digitBlocks("(A)*POW(2,-1074)".replace("A", "(1-1)*4514")) === 1,
    "digitBlocks POW 白名单",
  )

  console.log(`\n========== smoke: ${pass} 通过, ${fail} 失败 ==========`)
  process.exit(fail ? 1 : 0)
}
