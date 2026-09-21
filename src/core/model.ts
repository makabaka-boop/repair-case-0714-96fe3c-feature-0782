import { BREAK, CONFLICT, NONE, SAME, type DocModel, type Edge, type ParseError } from './types';

export const MIN_PAGE_HEIGHT = 1;
export const MAX_PAGE_HEIGHT = 10000;
export const MIN_BLOCKS = 1;
export const MAX_BLOCKS = 200_000;

/**
 * 严格校验并规范化用户导入的 JSON 数据。
 * 任何不合法输入都返回错误信息；调用方负责在出错时保留当前文档与已采纳版本。
 *
 * 数据约定见 README：顶层对象 { pageHeight, backPageHeight?, blocks }，
 * 块对象 { id, height, breakAfter?, sameAfter? }，最后一块上的标记被忽略。
 * 省略 backPageHeight 时为单面模式，解析/计算/导出与旧版逐项一致。
 * 重新导入本工具导出的文件时，多余字段（pages/cost 等）一律忽略。
 */
export function parseDoc(raw: unknown): { ok: true; model: DocModel } | { ok: false; error: ParseError } {
  if (typeof raw !== 'object' || raw === null || Array.isArray(raw)) {
    return { ok: false, error: { message: '顶层必须是一个 JSON 对象' } };
  }
  const obj = raw as Record<string, unknown>;

  const pageHeight = obj.pageHeight;
  if (typeof pageHeight !== 'number' || !Number.isInteger(pageHeight)) {
    return { ok: false, error: { message: 'pageHeight 必须是整数' } };
  }
  if (pageHeight < MIN_PAGE_HEIGHT || pageHeight > MAX_PAGE_HEIGHT) {
    return { ok: false, error: { message: `pageHeight 必须在 ${MIN_PAGE_HEIGHT} 到 ${MAX_PAGE_HEIGHT} 之间` } };
  }

  // backPageHeight 可选：存在（非 undefined）才启用双面模式，null 等仍属非法。
  let backPageHeight: number | undefined;
  if (obj.backPageHeight !== undefined) {
    if (typeof obj.backPageHeight !== 'number' || !Number.isInteger(obj.backPageHeight)) {
      return { ok: false, error: { message: 'backPageHeight 必须是整数' } };
    }
    if (obj.backPageHeight < MIN_PAGE_HEIGHT || obj.backPageHeight > MAX_PAGE_HEIGHT) {
      return { ok: false, error: { message: `backPageHeight 必须在 ${MIN_PAGE_HEIGHT} 到 ${MAX_PAGE_HEIGHT} 之间` } };
    }
    backPageHeight = obj.backPageHeight;
  }
  // 块高允许到两面容量的较大值（块只会在放得下它的那一面成页）。
  const maxHeight = backPageHeight === undefined ? pageHeight : Math.max(pageHeight, backPageHeight);

  const rawBlocks = obj.blocks;
  if (!Array.isArray(rawBlocks)) {
    return { ok: false, error: { message: 'blocks 必须是数组' } };
  }
  const n = rawBlocks.length;
  if (n < MIN_BLOCKS || n > MAX_BLOCKS) {
    return { ok: false, error: { message: `blocks 数量必须在 ${MIN_BLOCKS} 到 ${MAX_BLOCKS} 之间` } };
  }

  const blocks: DocModel['blocks'] = [];
  const seen = new Set<string>();
  for (let i = 0; i < n; i++) {
    const rb = rawBlocks[i] as unknown;
    const where = `第 ${i + 1} 项`;
    if (typeof rb !== 'object' || rb === null || Array.isArray(rb)) {
      return { ok: false, error: { message: `${where}：必须是对象` } };
    }
    const b = rb as Record<string, unknown>;

    if (!('id' in b)) {
      return { ok: false, error: { message: `${where}：缺少 id` } };
    }
    const id = b.id;
    if (typeof id !== 'string' && typeof id !== 'number') {
      return { ok: false, error: { message: `${where}：id 必须是字符串或数字` } };
    }
    const key = typeof id === 'number' ? `n:${String(id)}` : `s:${id}`;
    if (seen.has(key)) {
      return { ok: false, error: { message: `${where}：id 重复（${String(id)}）` } };
    }
    seen.add(key);

    const height = b.height;
    if (typeof height !== 'number' || !Number.isInteger(height)) {
      return { ok: false, error: { message: `${where}：height 必须是整数` } };
    }
    if (height < 1 || height > maxHeight) {
      return {
        ok: false,
        error: { message: `${where}：height 必须在 1 到 ${maxHeight}(两面页容量较大值) 之间` },
      };
    }

    let edge: Edge = NONE;
    if (i < n - 1) {
      const hasBreak = b.breakAfter === true;
      const hasSame = b.sameAfter === true;
      if (b.breakAfter !== undefined && typeof b.breakAfter !== 'boolean') {
        return { ok: false, error: { message: `${where}：breakAfter 必须是布尔值` } };
      }
      if (b.sameAfter !== undefined && typeof b.sameAfter !== 'boolean') {
        return { ok: false, error: { message: `${where}：sameAfter 必须是布尔值` } };
      }
      edge = hasBreak && hasSame ? CONFLICT : hasBreak ? BREAK : hasSame ? SAME : NONE;
    }
    blocks.push({ id, height, edge });
  }

  // 仅在提供 backPageHeight 时写入该键：省略字段的旧文件解析后结构逐项不变。
  const model: DocModel =
    backPageHeight === undefined
      ? { pageHeight, blocks }
      : { pageHeight, backPageHeight, blocks };
  return { ok: true, model };
}

/** 边界 i 的两个标记是否同置。 */
export function isConflict(edge: Edge): boolean {
  return edge === CONFLICT;
}

/** 列出所有冲突边界（块下标），空数组表示无冲突。 */
export function findConflicts(model: DocModel): number[] {
  const out: number[] = [];
  for (let i = 0; i < model.blocks.length - 1; i++) {
    if (model.blocks[i].edge === CONFLICT) out.push(i);
  }
  return out;
}
