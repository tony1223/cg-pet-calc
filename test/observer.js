'use strict'

// 「噬生・魔物觀測者」比對模式的回歸測試。
//
// 這個模式跟原本的 exact 差在**容差擺哪裡**：能力值一律精確比對，
// 容差只加在檔次上，而且只在該軸檔次落在 fullRates 五週期不規則處
// （`% 5 ∈ {0, 1}`）時才放寬。所以它是 exact 的**超集**，不是另一套演算法。
//
// 兩件事必須同時成立，這個模式才算對：
//   1. 不會弄丟 exact 找得到的解（superset）
//   2. exact 的整數列舉無解時它接得住（純白液態史萊姆 59 級就是這種案例）

import assert from 'assert'
import {RealGuess, PetDefaultData} from "../index.js"
import {observerTolerance, tierNudges, OBSERVER_TOL_MIN, OBSERVER_TOL_MAX} from "../lib/Pets.mjs"
import {fullRates} from "../lib/Utils.mjs"

/** 一組解的識別鍵 —— 檔次 ＋ 加點 ＋ 隨機檔就唯一決定一組解。 */
function key(r) {
    return [r.GuessRange.toArray(), r.ManualPoints, r.RandomRange].join('|');
}

function guess(name, params, opts) {
    const r = RealGuess(PetDefaultData, name, ...params, undefined, opts);
    assert.ok(r.pet.find, `圖鑑裡沒有 ${name}`);
    return r.results;
}

// [名稱, [lvl, hp, mp, atk, def, agi, notorderpoint], 預期解數]
//
// `want` 是拿同一套規則獨立實作的 Rust 版（魔物觀測-remake 的 petcalc）跑出來的數字。
// 兩邊各自列舉、各自取整，解數還一樣才代表規則真的搬對了 —— 這是這份測試最有價值的一條。
const CASES = [
    ['純白液態史萊姆', [59, 1815, 701, 280, 189, 140, 13], {exact: 0, observer: 4, nudged: 4}],
    ['聖誕水藍鼠', [98, 2308, 1327, 935, 328, 281, 0], {exact: 3, observer: 16, nudged: 13}],
];

describe('observer match mode', function () {
    this.timeout(60000);

    describe('observerTolerance()', () => {
        it('是 (當前等級 − 入手等級) / 200，夾在 0.01 與 0.1 之間', () => {
            // 沒填入手等級 → 等級差就是當前等級
            assert.strictEqual(observerTolerance(59, 0), OBSERVER_TOL_MAX); // 0.295 → 夾上界
            assert.ok(Math.abs(observerTolerance(45, 40) - 0.025) < 1e-12); // 5/200，界內
            assert.strictEqual(observerTolerance(42, 40), OBSERVER_TOL_MIN); // 2/200 = 0.01，剛好在下界
            assert.strictEqual(observerTolerance(41, 40), OBSERVER_TOL_MIN); // 0.005 → 夾下界
        });
    });

    describe('tierNudges()', () => {
        it('三個分支各如其所述，且第一個偏移量恆為 0', () => {
            const tol = 0.1;
            assert.deepStrictEqual(tierNudges(50, tol), [0, -tol, tol]); // % 5 === 0
            assert.deepStrictEqual(tierNudges(51, tol), [0, -tol]);      // % 5 === 1
            assert.deepStrictEqual(tierNudges(52, tol), [0]);
            assert.deepStrictEqual(tierNudges(53, tol), [0]);
            assert.deepStrictEqual(tierNudges(54, tol), [0]);
            // n = 0 與 n = 1 是特例：0 不是「多半階」那種，1 走 % 5 === 1 那條
            assert.deepStrictEqual(tierNudges(0, tol), [0]);
            assert.deepStrictEqual(tierNudges(1, tol), [0, -tol]);

            for (let n = 0; n <= 110; n++) {
                assert.strictEqual(tierNudges(n, tol)[0], 0, `檔次 ${n} 的第一個偏移量不是 0`);
            }
        });

        it('放寬的檔次恰好是 fullRates 不規則的地方', () => {
            // 規律處相鄰兩筆差 0.04；不規律處差 0.045 或 0.05。
            // 這條斷言把 tierNudges 綁死在表上 —— 表一改，這裡就會紅。
            //
            // 從 2 起跳：n = 1 的每階看起來規律（0 → 0.04），但那是因為
            // fullRates[0] 被特判成 0（閉合式的 floor((n-1)/5) 在 n = 0 會得 -1）。
            // 特判就住在 n = 1 這一階上，原程式的 mod-5 分類也照樣把它算成不規則。
            for (let n = 2; n <= 110; n++) {
                const step = Math.round((fullRates[n] - fullRates[n - 1]) * 1000) / 1000;
                const regular = step === 0.04;
                const nudged = tierNudges(n, 0.1).length > 1;
                assert.strictEqual(nudged, !regular,
                    `檔次 ${n}：step=${step} 但 nudges=${tierNudges(n, 0.1).length}`);
            }
        });
    });

    describe('與 exact 的關係', () => {
        for (const [name, params, want] of CASES) {
            it(`${name} ${params.join(' ')} — observer 是 exact 的超集`, () => {
                const exact = guess(name, params, {mode: 'exact'});
                const observer = guess(name, params, {mode: 'observer'});

                // exact 的整數列舉無解時會退到連續可行性回退（isApproximate），
                // 那是另一套演算法，不在這條斷言的範圍內。
                const exactInt = exact.filter(r => !r.isApproximate);
                const seen = new Set(observer.map(key));
                for (const r of exactInt) {
                    assert.ok(seen.has(key(r)), `observer 弄丟了 exact 的解 ${key(r)}`);
                }

                // 而且不靠偏移就成立的那些，必須跟 exact 的整數解一模一樣 ——
                // 多出來的每一組都要能指出是哪一軸的偏移換來的。
                const plain = observer.filter(r => !r.isNudged && !r.isApproximate);
                assert.deepStrictEqual(
                    plain.map(key).sort(), exactInt.map(key).sort(),
                    'observer 不靠偏移的解跟 exact 對不起來');

                // 跟 Rust 版對數字
                assert.strictEqual(exactInt.length, want.exact, 'exact 解數與 Rust 版對不起來');
                assert.strictEqual(observer.length, want.observer, 'observer 解數與 Rust 版對不起來');
                assert.strictEqual(observer.filter(r => r.isNudged).length, want.nudged,
                    '靠偏移的解數與 Rust 版對不起來');
            });
        }

        it('純白液態史萊姆 59 級：exact 的整數列舉無解，observer 接得住', () => {
            // 整個容差模型就是為了這個案例存在的。
            const [name, params] = CASES[0];
            const exact = guess(name, params, {mode: 'exact'});
            const observer = guess(name, params, {mode: 'observer'});

            assert.strictEqual(exact.filter(r => !r.isApproximate).length, 0,
                'exact 的整數列舉居然有解了 —— 這個案例不再能證明容差的必要性');
            assert.ok(observer.length > 0, 'observer 也推不出來');
            assert.ok(observer.every(r => r.isNudged), 'observer 的解應該全部靠偏移');
        });
    });

    // ── auto ─────────────────────────────────────────────────────────────────
    //
    // observer 單開是「一律套容差」，跟 Rust 版的 MatchMode::Observer 一樣照搬
    // 原程式的階梯：第一階有解就回傳。這有個後果 —— 第一階靠容差湊出解時，
    // 第二階本來要給的精確解就再也拿不到了（紫翎 9 級：exact 退到第二階拿 31 組，
    // observer 在第一階湊出 5 組就收工，兩邊完全不相交）。
    //
    // auto 就是為了這個存在的：精確的兩階先跑完，全空了才升級到容差。
    describe('auto', () => {
        // [名稱, 參數, exact 有沒有解]
        const LADDER_CASES = [
            ['紫翎', [9, 225, 311, 42, 56, 71, 0], true],           // exact 靠第二階才有解
            ['純白液態史萊姆', [59, 1815, 701, 280, 189, 140, 13], false], // exact 整數列舉全空
            ['聖誕水藍鼠', [98, 2308, 1327, 935, 328, 281, 0], true],
            ['紅帽哥布林', [1, 97, 68, 42, 39, 31, 0], true],        // 等級 1
        ];

        for (const [name, params, exactHasSolution] of LADDER_CASES) {
            it(`${name} ${params[0]} 級：auto 不會弄丟 exact 的解`, () => {
                const exact = guess(name, params, {mode: 'exact'});
                const auto = guess(name, params, {mode: 'auto'});

                const exactInt = exact.filter(r => !r.isApproximate);
                assert.strictEqual(exactInt.length > 0, exactHasSolution,
                    'exact 有沒有解跟這個案例的前提對不上，案例要重挑');

                const seen = new Set(auto.map(key));
                assert.deepStrictEqual(
                    exactInt.filter(r => !seen.has(key(r))).map(key), [],
                    'auto 弄丟了 exact 的解');
            });
        }

        it('exact 有解時，auto 一步都不放寬', () => {
            // 這條決定了 blast radius：exact 算得出來的案例，auto 的輸出完全不變。
            const [name, params] = [LADDER_CASES[0][0], LADDER_CASES[0][1]];
            assert.deepStrictEqual(
                guess(name, params, {mode: 'auto'}).map(key).sort(),
                guess(name, params, {mode: 'exact'}).map(key).sort());
        });

        it('exact 無解時，auto 退到跟 observer 一樣', () => {
            const [name, params] = CASES[0];  // 純白液態史萊姆 59 級
            assert.deepStrictEqual(
                guess(name, params, {mode: 'auto'}).map(key).sort(),
                guess(name, params, {mode: 'observer'}).map(key).sort());
        });

        it('紫翎 9 級就是 observer 單開會踩到的那顆地雷', () => {
            // 反過來釘住：observer 確實會弄丟解。這不是 bug，是照搬原程式的階梯，
            // 但也正因為如此，對外的預設不該是 observer。
            const [name, params] = [LADDER_CASES[0][0], LADDER_CASES[0][1]];
            const exactInt = guess(name, params, {mode: 'exact'}).filter(r => !r.isApproximate);
            const observer = guess(name, params, {mode: 'observer'});

            const seen = new Set(observer.map(key));
            assert.ok(exactInt.some(r => !seen.has(key(r))),
                'observer 居然沒弄丟解 —— 階梯行為變了，auto 的存在理由要重新確認');
        });
    });

    describe('預設值', () => {
        it('不指定 mode 時跟原本完全一樣', () => {
            const [name, params] = CASES[1];
            assert.deepStrictEqual(
                guess(name, params, undefined).map(key),
                guess(name, params, {mode: 'exact'}).map(key));
        });
    });
});
