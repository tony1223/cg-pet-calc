'use strict'

// 成長係數表的回歸測試。
//
// 這張表的權威來源是「噬生・魔物觀測者」monster.exe 的 double 表
// （VA 0x0058EA14 / file offset 0x18D614，111 筆 f64，index 0..110）。
//
// 修正前這裡只有 53 筆，而且 51/52 寫成 2.04 / 2.08 —— 比 50 的 2.095 還小，
// 破壞了原表的單調遞增。檔次 > 52 則直接查到 undefined，整條計算變 NaN。

import {fullRates, fullRatesFormula} from "../lib/Utils.mjs"
import {GrowRange} from "../lib/Pets.mjs"
import assert from 'assert'

describe('fullRates', function () {

    it('涵蓋 index 0..110 共 111 筆', () => {
        const keys = Object.keys(fullRates).map(Number).sort((a, b) => a - b);
        assert.strictEqual(keys.length, 111);
        assert.strictEqual(keys[0], 0);
        assert.strictEqual(keys[110], 110);
        for (let n = 0; n <= 110; n++) {
            assert.strictEqual(typeof fullRates[n], 'number', `檔次 ${n} 查不到`);
        }
    });

    it('嚴格單調遞增', () => {
        for (let n = 1; n <= 110; n++) {
            assert.ok(fullRates[n] > fullRates[n - 1],
                `檔次 ${n} (${fullRates[n]}) 沒有比 ${n - 1} (${fullRates[n - 1]}) 大`);
        }
    });

    it('每一筆都符合閉合式', () => {
        for (let n = 0; n <= 110; n++) {
            assert.ok(Math.abs(fullRates[n] - fullRatesFormula(n)) < 1e-9,
                `檔次 ${n}: 表 ${fullRates[n]} vs 公式 ${fullRatesFormula(n)}`);
        }
    });

    // 釘死曾經寫錯的那兩筆
    it('51 / 52 是 2.14 / 2.18，不是 2.04 / 2.08', () => {
        assert.strictEqual(fullRates[51], 2.14);
        assert.strictEqual(fullRates[52], 2.18);
    });

    it('表尾是 4.615', () => {
        assert.strictEqual(fullRates[110], 4.615);
    });

    // 這是修正前實際會壞掉的行為：高檔次寵物整條算出 NaN
    it('高檔次寵物不再算出 NaN', () => {
        for (const tier of [53, 60, 80, 110]) {
            const r = new GrowRange(tier, tier, tier, tier, tier, 0.2).calcBPAtLevel(100, null);
            const s = r.baseBP.calcRealNum();
            assert.ok(Number.isFinite(r.sumBaseBP), `檔次 ${tier} 的 sumBaseBP 是 ${r.sumBaseBP}`);
            assert.ok(Number.isFinite(s.hp), `檔次 ${tier} 的 hp 是 ${s.hp}`);
            assert.ok(s.hp > 0, `檔次 ${tier} 的 hp 是 ${s.hp}`);
        }
    });

    it('檔次越高，同等級能力越高', () => {
        let prev = -Infinity;
        for (let tier = 0; tier <= 110; tier++) {
            const hp = new GrowRange(tier, 0, 0, 0, 0, 0.2)
                .calcBPAtLevel(100, null).baseBP.calcRealNum().hp;
            assert.ok(hp >= prev, `檔次 ${tier} 的 hp (${hp}) 比 ${tier - 1} (${prev}) 低`);
            prev = hp;
        }
    });
});
