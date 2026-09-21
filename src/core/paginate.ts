import { BREAK, CONFLICT, NONE, SAME, type DocModel, type Edge, type PaginateOutcome } from './types';
import { findConflicts } from './model';

/**
 * 精确分页：在满足全部边界标记的前提下，最小化 Σ(每页剩余高度)²。
 *
 * 单面模式（model.backPageHeight 省略）：全部页容量同为 H，走 {@link paginateSingle}，
 * 解析/计算/页面与导出结构与旧版逐项一致。
 *
 * 双面模式（model.backPageHeight 存在）：第 1 页为正面（容量 Hf），此后正反交替
 * （容量 Hb）。令 dpF[i]/dpB[i] 分别表示「前 i 块排完、末页为正/背面」的最小代价，
 * 起点用虚拟态 dpB[0]=0（0 页之后接正面）：
 *
 *   dpF[i] = min over 合法 j: dpB[j] + (Hf − S[i] + S[j])²
 *   dpB[i] = min over 合法 j: dpF[j] + (Hb − S[i] + S[j])²
 *
 * 两条递推各自是与单面完全同形的直线查询，用**两个独立的凸包单调队列**做到均摊
 * O(n)：正面队列的线来自可行的 dpB[j]，背面队列的线来自可行的 dpF[j]。
 * 不按页数展开状态，也不存在「先用单一容量分页再校验奇偶」的回退。
 */
export function paginate(model: DocModel): PaginateOutcome {
  return model.backPageHeight === undefined
    ? paginateSingle(model)
    : paginateDuplex(model, model.pageHeight, model.backPageHeight);
}

/** 单面精确分页：全部页容量同为 H，滑动窗口凸包 DP。 */
function paginateSingle(model: DocModel): PaginateOutcome {
  const H = model.pageHeight;
  const blocks = model.blocks;
  const n = blocks.length;

  const conflicts = findConflicts(model);
  if (conflicts.length > 0) {
    return { ok: false, error: { kind: 'conflict', conflicts } };
  }

  // 被「同页」链串起来的连续块若总高超过页容量，则无解。
  const overflow = findSameOverflow(model, H, undefined);
  if (overflow) {
    return {
      ok: false,
      error: { kind: 'unsat', reason: overflow.reason, start: overflow.start, end: overflow.end },
    };
  }

  // 前缀和：最大 200000 × 10000 = 2e9，Number 安全整数范围内。
  const S = new Float64Array(n + 1);
  for (let i = 0; i < n; i++) S[i + 1] = S[i] + blocks[i].height;

  const edgeAt = (i: number): Edge => (i < n - 1 ? blocks[i].edge : NONE);
  /** 起点 j 可作页首：j=0 恒可；j>0 要求前边界 edge(j-1) 不是 SAME。 */
  const canStart = (j: number): boolean => j === 0 || edgeAt(j - 1) !== SAME;
  /** 终点 i 可作页尾：i=n 恒可；i<n 要求尾边界 edge(i-1) 不是 SAME。 */
  const canEnd = (i: number): boolean => i === n || edgeAt(i - 1) !== SAME;

  const dp = new Float64Array(n + 1).fill(Number.POSITIVE_INFINITY);
  const parent = new Int32Array(n + 1).fill(-1);

  // 凸包队列，存直线下标 j。
  const hull = new Int32Array(n + 2);
  let head = 0;
  let tail = 0;

  // b_j 与 -m_j = 2S[j]（恒正、严格递增）。b 最大约 4e18，在 int64 内。
  const bArr = new BigInt64Array(n + 1);
  const neg2m = new Float64Array(n + 1);

  /**
   * b 相对 a、c 是否全局冗余：x(a,b) ≥ x(b,c)
   * 等价于 (b_c-b_a)(nm_b-nm_a) ≤ (b_b-b_a)(nm_c-nm_a)，nm=-m。
   */
  const redundant = (a: number, b: number, c: number): boolean => {
    const lhs = (bArr[c] - bArr[a]) * BigInt(Math.round(neg2m[b] - neg2m[a]));
    const rhs = (bArr[b] - bArr[a]) * BigInt(Math.round(neg2m[c] - neg2m[a]));
    return lhs <= rhs;
  };

  /**
   * 前驱线 a 因容量滑出可行窗口的横坐标：S[i] − S[a] ≤ H ⟺ x ≤ H + S[a]。
   * 强制分页不会分裂队内三元组：edge ≥ a 的 BREAK 会把 L 推过 a，每次迭代
   * 查询前的队首淘汰已将其移出队列；更靠后的 BREAK 只会让 a、b、c 同时过期。
   */
  const expiryX = (a: number): bigint => BigInt(H) + BigInt(Math.round(S[a]));

  /**
   * 滑动窗口下中线 b 可安全删除的条件：全局冗余，且后线 c 的接管点不晚于
   * 前驱线 a 的失效横坐标（x(b,c) ≤ H + S[a]，即 b_c−b_b ≤ (H+S[a])·(nm_c−nm_b)）。
   * 否则 a 因容量过期后，b 会在可行集内重新最优
   * （反例：H=5、高度 [2,3,1]，误删会得到代价 16 而非最优 10）。
   */
  const removable = (a: number, b: number, c: number): boolean => {
    if (!redundant(a, b, c)) return false;
    return bArr[c] - bArr[b] <= expiryX(a) * BigInt(Math.round(neg2m[c] - neg2m[b]));
  };

  /** 队首查询：在 x 处 b(第二线) 不差于 a(第一线)。 */
  const frontWorse = (a: number, b: number, x: number): boolean => {
    return bArr[b] - bArr[a] <= BigInt(Math.round(x)) * BigInt(Math.round(neg2m[b] - neg2m[a]));
  };

  const pushLine = (j: number) => {
    bArr[j] = BigInt(Math.round(dp[j])) + 2n * BigInt(H) * BigInt(Math.round(S[j])) + BigInt(Math.round(S[j])) ** 2n;
    neg2m[j] = 2 * S[j];
    while (tail - head >= 2 && removable(hull[tail - 2], hull[tail - 1], j)) {
      tail--;
    }
    hull[tail++] = j;
  };

  dp[0] = 0;
  pushLine(0);

  let capPtr = 0; // 最小满足 S[i]-S[capPtr] ≤ H 的下标
  let lastBreakPlus = 0; // 最后一个 BREAK（edge(k-1)）要求 j ≥ k+1

  for (let i = 1; i <= n; i++) {
    if (i > 1 && edgeAt(i - 2) === BREAK) {
      lastBreakPlus = i - 1;
    }
    while (S[i] - S[capPtr] > H) capPtr++;
    const L = Math.max(capPtr, lastBreakPlus);

    // 队首过期（容量/分页下界，可能一次跨越多条）或已被后线接管。
    while (
      tail - head >= 1 &&
      (hull[head] < L || (tail - head >= 2 && frontWorse(hull[head], hull[head + 1], S[i])))
    ) {
      head++;
    }

    if (canEnd(i) && tail > head) {
      const j = hull[head];
      const rem = H - (S[i] - S[j]);
      dp[i] = dp[j] + rem * rem;
      parent[i] = j;
    }

    if (i < n && canStart(i) && Number.isFinite(dp[i])) {
      pushLine(i);
    }
  }

  if (!Number.isFinite(dp[n]) || parent[n] < 0) {
    return {
      ok: false,
      error: { kind: 'unsat', reason: '不存在满足全部边界约束的分页方案', start: 0, end: n },
    };
  }

  const pages = [];
  let cur = n;
  while (cur > 0) {
    const j = parent[cur];
    const used = S[cur] - S[j];
    pages.push({ start: j, end: cur, used, remaining: H - used });
    cur = j;
  }
  pages.reverse();

  return { ok: true, result: { pages, cost: Math.round(dp[n]) } };
}

/**
 * 双面精确分页：第 1 页正面（Hf），此后正反交替（Hb）。
 * 两条奇偶 DP 各自维护一个与单面同构的滑动窗口凸包，全程 O(n)。
 */
function paginateDuplex(model: DocModel, Hf: number, Hb: number): PaginateOutcome {
  const blocks = model.blocks;
  const n = blocks.length;

  const conflicts = findConflicts(model);
  if (conflicts.length > 0) {
    return { ok: false, error: { kind: 'conflict', conflicts } };
  }

  // 同页链必须落进「某一个面」的某一页；总高超过两面容量的较大值才必然无解，
  // 故线性预检按较大容量判；奇偶导致的不可行（链只放得下正面却轮到背面）由 DP 兜底。
  const overflow = findSameOverflow(model, Math.max(Hf, Hb), Math.min(Hf, Hb));
  if (overflow) {
    return {
      ok: false,
      error: { kind: 'unsat', reason: overflow.reason, start: overflow.start, end: overflow.end },
    };
  }

  // 前缀和：最大 200000 × 10000 = 2e9，Number 安全整数范围内。
  const S = new Float64Array(n + 1);
  for (let i = 0; i < n; i++) S[i + 1] = S[i] + blocks[i].height;

  const edgeAt = (i: number): Edge => (i < n - 1 ? blocks[i].edge : NONE);
  /** 起点 j 可作页首：j=0 恒可；j>0 要求前边界 edge(j-1) 不是 SAME。 */
  const canStart = (j: number): boolean => j === 0 || edgeAt(j - 1) !== SAME;
  /** 终点 i 可作页尾：i=n 恒可；i<n 要求尾边界 edge(i-1) 不是 SAME。 */
  const canEnd = (i: number): boolean => i === n || edgeAt(i - 1) !== SAME;

  // dpF：末页为正面的最优代价（页数奇）；dpB：末页为背面（页数偶）。
  const dpF = new Float64Array(n + 1).fill(Number.POSITIVE_INFINITY);
  const dpB = new Float64Array(n + 1).fill(Number.POSITIVE_INFINITY);
  // 两条递推各自的回溯起点（parentF[i] 给出 dpF[i] 选中的 j；依面别交替回溯）。
  const parentF = new Int32Array(n + 1).fill(-1);
  const parentB = new Int32Array(n + 1).fill(-1);
  // 同一下标 j 可同时作为两个队列的线，但截距不同（来源 dp、面容量都不同），
  // 必须各存一份；交叉比较全部 BigInt（S² 可达 4e18）。
  const bFront = new BigInt64Array(n + 1);
  const bBack = new BigInt64Array(n + 1);

  interface Hull {
    cap: number;
    b: BigInt64Array;
    lines: Int32Array;
    head: number;
    tail: number;
  }
  // frontHull：线来自可行的 dpB 起点，本页按 Hf 成页；backHull 反之。
  const frontHull: Hull = { cap: Hf, b: bFront, lines: new Int32Array(n + 2), head: 0, tail: 0 };
  const backHull: Hull = { cap: Hb, b: bBack, lines: new Int32Array(n + 2), head: 0, tail: 0 };

  /**
   * b 相对 a、c 是否全局冗余：x(a,b) ≥ x(b,c)。
   * 斜率差为 2(S[b]−S[a])。
   */
  const redundant = (h: Hull, ai: number, bi: number, ci: number): boolean => {
    const a = h.lines[ai];
    const b = h.lines[bi];
    const c = h.lines[ci];
    const lhs = (h.b[c] - h.b[a]) * BigInt(Math.round(S[b] - S[a]));
    const rhs = (h.b[b] - h.b[a]) * BigInt(Math.round(S[c] - S[a]));
    return lhs <= rhs;
  };

  /** 前驱线 a 因容量滑出窗口的横坐标：x ≤ cap + S[a]。 */
  const expiryX = (h: Hull, a: number): bigint => BigInt(h.cap) + BigInt(Math.round(S[a]));

  /**
   * 滑动窗口下中线 b 可安全删除：全局冗余，且后线 c 的接管点不晚于前驱线 a 的
   * 失效横坐标（与单面同一关键正确性点：H=5、高度 [2,3,1] 的反例同样适用）。
   * 斜率差为 2(S[c]−S[b])，系数 2 不可漏（漏掉会使判定偏保守、保留非凸中线，
   * 大高度差下队首被卡在非最优线：1200 块 Hf=100/Hb=60 时 i=84 失真）。
   */
  const removable = (h: Hull, ai: number, bi: number, ci: number): boolean => {
    if (!redundant(h, ai, bi, ci)) return false;
    const a = h.lines[ai];
    const b = h.lines[bi];
    const c = h.lines[ci];
    return h.b[c] - h.b[b] <= expiryX(h, a) * BigInt(Math.round(2 * (S[c] - S[b])));
  };

  /** 队首查询：在 x 处 b(第二线) 不差于 a(第一线)。 */
  const frontWorse = (h: Hull, x: number): boolean => {
    const a = h.lines[h.head];
    const b = h.lines[h.head + 1];
    return h.b[b] - h.b[a] <= BigInt(Math.round(x)) * BigInt(Math.round(2 * (S[b] - S[a])));
  };

  /**
   * 把起点 j（来源代价 srcDp，本页按 h.cap 成页）推进凸包。
   * 冗余判定读的是队尾槽位中的线，故先把 j 放入 h.lines[tail]；每弹出一条
   * 中线，j 都要随尾指针左移一格——否则多连弹时三元组末端仍是已弹出的旧线。
   * 若不预放（直接传裸下标给只认槽位的 removable），会读到陈旧槽位而误删中线
   * （fuzz：Hf=Hb=7、[3,2,5,1,4,6] 得 15 而非 13）。
   */
  const pushLine = (h: Hull, j: number, srcDp: number) => {
    const sj = S[j];
    h.b[j] =
      BigInt(Math.round(srcDp)) + 2n * BigInt(h.cap) * BigInt(Math.round(sj)) + BigInt(Math.round(sj)) ** 2n;
    h.lines[h.tail] = j;
    while (h.tail - h.head >= 2 && removable(h, h.tail - 2, h.tail - 1, h.tail)) {
      h.tail--;
      h.lines[h.tail] = j; // 新线随尾指针左移，保证下一三元组末端仍是 j
    }
    h.tail++;
  };

  /** 队首过期（容量/分页下界，可能一次跨越多条）或已被后线接管。 */
  const evict = (h: Hull, L: number, x: number) => {
    while (
      h.tail - h.head >= 1 &&
      (h.lines[h.head] < L || (h.tail - h.head >= 2 && frontWorse(h, x)))
    ) {
      h.head++;
    }
  };

  // 虚拟态：0 块、0 页（视作「末页为背面」），只向正面队列投放起点 0。
  dpB[0] = 0;
  pushLine(frontHull, 0, 0);

  // 容量下界游标（独立于凸包增删，对全部起点下标单调推进）。
  let frontCapPtr = 0;
  let backCapPtr = 0;
  let lastBreakPlus = 0; // 最后一个 BREAK（edge(k-1)）要求 j ≥ k+1

  for (let i = 1; i <= n; i++) {
    if (i > 1 && edgeAt(i - 2) === BREAK) {
      lastBreakPlus = i - 1;
    }
    while (S[i] - S[frontCapPtr] > Hf) frontCapPtr++;
    while (S[i] - S[backCapPtr] > Hb) backCapPtr++;
    const Lf = Math.max(frontCapPtr, lastBreakPlus);
    const Lb = Math.max(backCapPtr, lastBreakPlus);

    if (canEnd(i)) {
      evict(frontHull, Lf, S[i]);
      evict(backHull, Lb, S[i]);

      // 两条递推互相独立；全局谁更优只在终点 n 处裁决。
      if (frontHull.tail > frontHull.head) {
        const j = frontHull.lines[frontHull.head];
        const rem = Hf - (S[i] - S[j]);
        dpF[i] = dpB[j] + rem * rem;
        parentF[i] = j;
      }
      if (backHull.tail > backHull.head) {
        const j = backHull.lines[backHull.head];
        const rem = Hb - (S[i] - S[j]);
        dpB[i] = dpF[j] + rem * rem;
        parentB[i] = j;
      }
    }

    if (i < n && canStart(i)) {
      // 面别相反的队列才接收该起点；无穷来源不投放。
      if (Number.isFinite(dpB[i])) pushLine(frontHull, i, dpB[i]);
      if (Number.isFinite(dpF[i])) pushLine(backHull, i, dpF[i]);
    }
  }

  const endFront = Number.isFinite(dpF[n]);
  const endBack = Number.isFinite(dpB[n]);
  if (!endFront && !endBack) {
    return {
      ok: false,
      error: { kind: 'unsat', reason: '不存在满足全部边界约束与正背面交替的分页方案', start: 0, end: n },
    };
  }

  // 平局优先以正面收尾：回溯确定且不影响最优性。
  const endOnFront = endFront && (!endBack || dpF[n] <= dpB[n]);
  const pages = [];
  let cur = n;
  let onFront = endOnFront;
  while (cur > 0) {
    const j = onFront ? parentF[cur] : parentB[cur];
    const cap = onFront ? Hf : Hb;
    const used = S[cur] - S[j];
    pages.push({
      start: j,
      end: cur,
      used,
      remaining: cap - used,
      side: onFront ? ('front' as const) : ('back' as const),
      capacity: cap,
    });
    cur = j;
    onFront = !onFront;
  }
  pages.reverse();
  // 第 1 页必须是正面（由 dpB[0]=0 虚拟态保证）；防御性校验。
  if (pages.length === 0 || pages[0].side !== 'front') {
    return {
      ok: false,
      error: { kind: 'unsat', reason: '内部错误：首页非正面', start: 0, end: n },
    };
  }

  const cost = Math.round(endOnFront ? dpF[n] : dpB[n]);
  return { ok: true, result: { pages, cost } };
}

/** 扫描同页链：连续被 SAME 连接的块若总高超过可容纳面，返回无解区间（半开，块下标）。 */
function findSameOverflow(
  model: DocModel,
  capacity: number,
  otherCapacity: number | undefined,
): { reason: string; start: number; end: number } | null {
  const { blocks } = model;
  const n = blocks.length;
  let i = 0;
  while (i < n) {
    let sum = blocks[i].height;
    let j = i;
    while (j < n - 1 && blocks[j].edge === SAME) {
      j++;
      sum += blocks[j].height;
    }
    if (sum > capacity) {
      const capText =
        otherCapacity === undefined
          ? `页容量 ${capacity}`
          : `正面容量 ${Math.max(capacity, otherCapacity)}、背面容量 ${Math.min(capacity, otherCapacity)}`;
      return {
        reason: `第 ${i + 1}–${j + 1} 块被「同页」标记强制连续，但总高度 ${sum} 超过${capText}，任何一面都放不下`,
        start: i,
        end: j + 1,
      };
    }
    i = j + 1;
  }
  return null;
}

export { NONE, BREAK, SAME, CONFLICT };
