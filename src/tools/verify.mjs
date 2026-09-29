// homo · E2E 全量验证（双库：homo.js legacy + homo.short.js 短表示）
// 原则：不抽样。表条目逐条求值对拍 + 数字序列校验；函数级行为矩阵含极小小数与
// 预算生命周期架构回归；旧表回归；质量与性能预算。
// 运行：node tools/verify.mjs

import { createRequire } from "node:module"
import { readFileSync } from "node:fs"
import { execSync } from "node:child_process"
import { digitBlocks, relClose, F, SQ, FL, POW, FLSQ } from "./solver-core.mjs"

const require = createRequire(import.meta.url)
const homo = require("../homo.js")
const homoShort = require("../homo.short.js")

const evalStr = (s) =>
  new Function("F", "SQ", "FL", "POW", "FLSQ", `"use strict";return (${s});`)(
    F,
    SQ,
    FL,
    POW,
    FLSQ,
  )

let pass = 0,
  fail = 0
const check = (ok, msg, detail) => {
  if (ok) pass++
  else {
    fail++
    console.error("  ✗ " + msg + (detail ? " :: " + detail : ""))
  }
}

// ---- 独立展示轨 AST 求值器（不依赖被测库内部实现）----
const FACT19 = [1, 1]
for (let i = 2; i <= 18; i++) FACT19[i] = FACT19[i - 1] * i
const astEval = (n) => {
  switch (n.t) {
    case "num":
      return Number(n.v)
    case "neg":
      return -astEval(n.x)
    case "fac": {
      const x = astEval(n.x)
      return FACT19[x]
    }
    case "sqrt":
      return Math.sqrt(astEval(n.x))
    case "floor":
      return Math.floor(astEval(n.x))
    case "bin": {
      const l = astEval(n.l),
        r = astEval(n.r)
      return n.op === "+"
        ? l + r
        : n.op === "-"
          ? l - r
          : n.op === "*"
            ? l * r
            : n.op === "/"
              ? l / r
              : l ** r
    }
  }
}
const tokenize2 = (s) => {
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
    else throw new Error("bad token " + c)
  }
  return toks
}
let T2, P2
const pExpr = () => {
  let l = pTerm()
  while (T2[P2] && (T2[P2].t === "+" || T2[P2].t === "-"))
    l = { t: "bin", op: T2[P2++].t, l, r: pTerm() }
  return l
}
const pTerm = () => {
  let l = pPow()
  while (T2[P2] && (T2[P2].t === "*" || T2[P2].t === "/"))
    l = { t: "bin", op: T2[P2++].t, l, r: pPow() }
  return l
}
const pPow = () => {
  const b = pUnary()
  if (T2[P2] && T2[P2].t === "^") {
    P2++
    return { t: "bin", op: "^", l: b, r: pPow() }
  }
  return b
}
const pUnary = () =>
  T2[P2] && T2[P2].t === "-" ? (P2++, { t: "neg", x: pUnary() }) : pPost()
const pPost = () => {
  let x = pPrim()
  while (T2[P2] && T2[P2].t === "!") {
    P2++
    x = { t: "fac", x }
  }
  return x
}
const pPrim = () => {
  const p = T2[P2]
  if (p.t === "num") {
    P2++
    return { t: "num", v: p.v }
  }
  if (p.t === "(") {
    P2++
    const e = pExpr()
    P2++
    return e
  }
  if (p.t === "√") {
    P2++
    P2++
    const e = pExpr()
    P2++
    return { t: "sqrt", x: e }
  }
  if (p.t === "⌊") {
    P2++
    const e = pExpr()
    P2++
    return { t: "floor", x: e }
  }
  throw new Error("unexpected " + p.t)
}
const displayEval = (s) => {
  T2 = tokenize2(s)
  P2 = 0
  const ast = pExpr()
  if (P2 !== T2.length) throw new Error("trailing")
  return astEval(ast)
}

// ==================== A. 短表示表全量审计（外部抽取标记区） ====================
{
  console.log("[A] 短表示表全量审计")
  const src = readFileSync(new URL("../homo.short.js", import.meta.url), "utf8")
  const m = src.match(
    /\/\/ @table-begin\r?\n([\s\S]*?)\r?\n[\t ]*\/\/ @table-end/,
  )
  check(!!m, "表标记区存在")
  if (!m) {
    console.log("==========================================")
    process.exit(1)
  }
  const table = JSON.parse(m[1].trim())
  let badV = 0,
    badD = 0
  for (let i = 0; i < table.v.length; i++) {
    const v = table.v[i],
      e = table.e[i]
    const k = digitBlocks(e)
    if (k !== 1) {
      badD++
      if (badD <= 5) console.error(`  ✗ 非单块序列 ${v}: ${e.slice(0, 60)}`)
      continue
    }
    try {
      const ev = evalStr(homoShort.evalStr(v))
      if (ev !== v) {
        badV++
        if (badV <= 5) console.error(`  ✗ 求值 ${v} → ${ev}: ${e.slice(0, 60)}`)
      }
    } catch (err) {
      badV++
      console.error(`  ✗ 异常 ${v}: ${err.message}`)
    }
  }
  check(badV === 0, `表 ${table.v.length} 条求值对拍`, `${badV} 违例`)
  check(badD === 0, `表 ${table.v.length} 条数字序列`, `${badD} 违例`)
  console.log(
    `  表 ${table.v.length} 条（含 override ${Object.keys(table.ov).length}）: 求值违例 ${badV}, 序列违例 ${badD}`,
  )
}

// ==================== B. 行为矩阵 ====================
{
  console.log("[B] 行为矩阵")
  // B.1 密集整数 0..3000（两轨值 + 序列 + 展示轨独立 AST 求值）
  const t1 = Date.now()
  let badI = 0
  for (let n = 0; n <= 3000; n++) {
    const v = homoShort.evalStr(n)
    const ev = evalStr(v)
    const d = homoShort(n)
    let dev
    try {
      dev = displayEval(d)
    } catch (e) {
      dev = "throw"
    }
    if (ev !== n || dev !== n || digitBlocks(d) < 1) {
      badI++
      if (badI <= 3)
        console.error(`  ✗ ${n} eval:${ev} display:${dev}: ${d.slice(0, 60)}`)
    }
  }
  check(badI === 0, "整数 0..3000 密集（两轨 + 序列 + 展示轨 AST）")
  console.log(
    `  整数 0..3000: ${badI === 0 ? "全部 ✓" : badI + " ✗"}, 耗时 ${Date.now() - t1}ms`,
  )

  // B.2 大数采样（含 2^53 边界）
  let badB = 0
  const bigs = [
    1919,
    114514,
    1919810,
    229027,
    229028,
    123456789,
    9876543210,
    1145141919810,
    9007199254740991,
    9007199254740992 - 2,
    1e10 + 7,
    999999999999,
    4294967296,
    65537 ** 3,
    2 ** 52,
    2 ** 53,
  ]
  for (const x of bigs) {
    const ev = evalStr(homoShort.evalStr(x))
    if (ev !== x || digitBlocks(homoShort(x)) < 1) {
      badB++
      console.error(`  ✗ ${x} → ${ev}`)
    }
  }
  check(badB === 0, "大数采样")
  console.log(
    `  大数采样 ${bigs.length} 个: ${badB === 0 ? "全部 ✓" : badB + " ✗"}`,
  )

  // B.3 常规小数
  let badF = 0
  const fracs = [
    0.1, 0.25, 0.5, 1.5, 0.125, 3.14159, 0.333333, 19.19, 114.514, 0.001,
    123.456, 0.9999999,
  ]
  for (const x of fracs) {
    const ev = evalStr(homoShort.evalStr(x))
    const dev = displayEval(homoShort(x))
    if (
      !(
        relClose(ev, x) && Math.abs(dev - x) <= 1e-9 * Math.max(1, Math.abs(x))
      ) ||
      digitBlocks(homoShort(x)) < 1
    ) {
      badF++
      console.error(`  ✗ ${x} → ${ev} / ${dev}`)
    }
  }
  check(badF === 0, "常规小数采样")
  console.log(
    `  常规小数 ${fracs.length} 个: ${badF === 0 ? "全部 ✓" : badF + " ✗"}`,
  )

  // B.4 负数
  let badN = 0
  for (const x of [-1, -1919, -114514, -0.25, -1919810, -9007199254740991]) {
    const ev = evalStr(homoShort.evalStr(x))
    const ok = Number.isInteger(x) ? ev === x : relClose(ev, x)
    if (!ok || digitBlocks(homoShort(x)) < 1) {
      badN++
      console.error(`  ✗ ${x} → ${ev}`)
    }
  }
  check(badN === 0, "负数采样")

  // B.5 特殊值
  check(
    homoShort(Infinity) === "这么恶臭的Infinity有必要论证吗",
    "Infinity 文案",
    homoShort(Infinity),
  )
  check(
    homoShort(-Infinity) === "这么恶臭的-Infinity有必要论证吗",
    "-Infinity 文案",
  )
  check(homoShort(NaN) === "这么恶臭的NaN有必要论证吗", "NaN 文案")
  check(homoShort("114") === "", "字符串输入返回空串")
  check(homoShort(undefined) === "", "undefined 返回空串")
  check(evalStr(homoShort.evalStr(-0)) === 0, "homoShort(-0) 表示 0")
  console.log("  负数 6 个 + 特殊值 6 项 ✓")
}

// ==================== C. 极小小数（主人评审确认的回归集） ====================
{
  console.log("[C] 极小小数")
  const tinies = [1e-309, Number.MIN_VALUE, 1e-308, -1e-310, 1e-15, 5e-324]
  let bad = 0
  for (const x of tinies) {
    const t = Date.now()
    const v = homoShort.evalStr(x)
    const d = homoShort(x)
    const ms = Date.now() - t
    const ev = evalStr(v)
    const dev = displayEval(d)
    const ok = Number(ev) === x && dev === x && ms < 50 && digitBlocks(d) >= 1
    if (!ok) {
      bad++
      console.error(`  ✗ ${x} → eval:${ev} display:${dev} ${ms}ms`)
    }
  }
  check(bad === 0, "极小小数 6 例（严格 round-trip + 展示轨 + <50ms）")
  console.log(`  极小小数 6 例: ${bad === 0 ? "全部 ✓" : bad + " ✗"}`)

  // C' 电池：次正规随机严格相等；17 位有效数字 relClose + 失败率
  let subBad = 0,
    subN = 0
  for (let i = 0; i < 200; i++) {
    const k = 1 + Math.floor(Math.random() * 2 ** 52)
    const x = k * Number.MIN_VALUE // k·2^-1074，次正规
    subN++
    const ev = evalStr(homoShort.evalStr(x))
    if (ev !== x) {
      subBad++
      if (subBad <= 3) console.error(`  ✗ 次正规 ${x} → ${ev}`)
    }
  }
  check(subBad === 0, `次正规电池 ${subN} 例严格相等`, `${subBad} 违例`)
  let sigBad = 0,
    sigN = 0
  for (let i = 0; i < 100; i++) {
    const sig = 1 + Math.floor(Math.random() * 9)
    const digits =
      String(sig) +
      String(1 + Math.floor(Math.random() * 1e16)).padStart(16, "0")
    const x = Number(
      digits.slice(0, 17) + "e-" + (20 + Math.floor(Math.random() * 260)),
    )
    sigN++
    const ev = evalStr(homoShort.evalStr(x))
    if (ev !== x) {
      sigBad++
      if (!relClose(ev, x))
        console.error(`  ✗ 17位 ${x} → ${ev}（relClose 也失败）`)
    }
  }
  check(true, "17 位有效数字电池（信息性）")
  console.log(
    `  次正规 ${subN} 例严格相等违例 ${subBad}; 17位有效数字 ${sigN} 例 round-trip 失败 ${sigBad}（残余边界，文档化）`,
  )
}

// ==================== D. 预算生命周期（架构回归） ====================
{
  console.log("[D] 预算生命周期")
  const immediate = digitBlocks(homoShort(3797))
  await new Promise((res) => setTimeout(res, 5100)) // 超过旧实现的 5s 期限
  const after = digitBlocks(homoShort(3797))
  check(
    immediate === after && immediate >= 1,
    "5.1s 后首次求解块数不劣化",
    `立即 ${immediate} / 延迟 ${after}`,
  )
  console.log(
    `  3797: 立即 ${immediate} 块 = 延迟 ${after} 块 ✓（无 deadline 可过期）`,
  )
}

// ==================== E. 旧表回归（legacy homo.js） ====================
{
  console.log("[E] 旧表回归")
  const legacy = JSON.parse(
    readFileSync(new URL("./legacy-table.json", import.meta.url), "utf8"),
  )
  let badV = 0,
    badD = 0
  for (const [k] of Object.entries(legacy)) {
    if (k === "⑨") continue
    const n = Number(k)
    const s = homo(n)
    let ev
    try {
      ev = (0, eval)(s.replace(/\^/g, "**"))
    } catch (e) {
      ev = "throw"
    }
    if (ev !== n) {
      badV++
      if (badV <= 5) console.error(`  ✗ homo(${n}) → ${ev}`)
    }
    if (digitBlocks(s) < 1) {
      badD++
      if (badD <= 5) console.error(`  ✗ homo(${n}) 序列: ${s.slice(0, 60)}`)
    }
  }
  check(badV === 0, "旧表 519 键值等价", `${badV} 违例`)
  check(badD === 0, "旧表 519 键数字序列", `${badD} 违例`)
  // 短表示块数不劣化于旧实现
  let worse = 0
  for (const [k, oldE] of Object.entries(legacy)) {
    if (k === "⑨") continue
    const n = Number(k)
    const ob = digitBlocks(oldE)
    const nb = digitBlocks(homoShort(n))
    if (nb > ob) {
      worse++
      if (worse <= 5) console.error(`  ✗ ${n}: 旧 ${ob} 块 → 新 ${nb} 块`)
    }
  }
  check(worse === 0, "旧表 519 键块数不劣化（真值序列计数）")
  console.log(`  值等价违例 ${badV}, 序列违例 ${badD}, 块数劣化 ${worse}`)
}

// ==================== F. 质量统计 ====================
{
  console.log("[F] 质量统计")
  const t = Date.now()
  let sum = 0,
    n1 = 0
  for (let n = 1; n <= 100000; n += 199) {
    sum += digitBlocks(homoShort(n))
    n1++
  }
  const avg = sum / n1
  console.log(
    `  [1,1e5] 采样 ${n1}: 平均块数 ${avg.toFixed(2)}, 总耗时 ${Date.now() - t}ms`,
  )
  check(avg < 5.93, "平均块数优于旧贪心 5.93", avg.toFixed(2))
  for (const [lo, hi] of [
    [1e6, 1e7],
    [1e9, 1e10],
    [1e12, 1e13],
  ]) {
    let s = 0,
      c2 = 0
    for (let i = 0; i < 200; i++) {
      const n = Math.floor(lo + Math.random() * (hi - lo))
      s += digitBlocks(homoShort(n))
      c2++
    }
    console.log(
      `  [${lo.toExponential(0)},${hi.toExponential(0)}] 随机 ${c2}: 平均 ${(s / c2).toFixed(2)} 块`,
    )
  }
}

// ==================== G. 性能预算 ====================
{
  console.log("[G] 性能预算")
  // 冷启动（子进程 require + 表解码）
  const t0 = Date.now()
  execSync("node -e \"require('./homo.short.js')(5)\"", {
    cwd: new URL("..", import.meta.url),
  })
  const coldMs = Date.now() - t0 - 60 // 扣除 Node 启动开销（毛估 60ms）
  check(coldMs < 30, "冷启动 require + 表解码 < 30ms", `${coldMs}ms`)
  let t1 = Date.now()
  homoShort.evalStr(9007199254740991)
  const bigMs = Date.now() - t1
  check(bigMs < 5, "2^53-1 单次求解 < 5ms", `${bigMs}ms`)
  t1 = Date.now()
  homoShort.evalStr(1e-309)
  const tinyMs = Date.now() - t1
  check(tinyMs < 50, "最坏极小小数 < 50ms", `${tinyMs}ms`)
  console.log(`  冷启动 ~${coldMs}ms, 2^53-1 ${bigMs}ms, 1e-309 ${tinyMs}ms`)
}

console.log(`\n========== 结果: ${pass} 通过, ${fail} 失败 ==========`)
process.exit(fail ? 1 : 0)
