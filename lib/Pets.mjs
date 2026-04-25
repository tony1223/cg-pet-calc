import {lusolve} from "mathjs";


import {sum, calcDiff, fullRates, minmax, GuessResultToString} from "./Utils.mjs";

// Inverse of the stat-from-bp matrix (rows: HP, MP, ATK, DEF, AGI; cols: hpp, attackp, defendp, agip, mpp).
// Used to algebraically solve for r given target stats and outer manual point allocation.
const M_INV = [
    [ 0.13249019, -0.00806319, -0.06785930, -0.10938981, -0.16408472],
    [-0.00782811, -0.00608853,  0.38607709, -0.02429143, -0.03643715],
    [-0.00695832, -0.00541203, -0.02719073,  0.34877798, -0.03238858],
    [-0.00467806, -0.00363849, -0.02954152, -0.02452651,  0.51876579],
    [-0.00935612,  0.10383413, -0.05908304, -0.04905303, -0.07357954],
];

// Forward stat-from-bp matrix (rows: HP, MP, ATK, DEF, AGI; cols: hpp, attackp, defendp, agip, mpp).
const M_BP = [
    [8, 2, 3, 3, 1],
    [1, 2, 2, 2, 10],
    [0.2, 2.7, 0.3, 0.3, 0.2],
    [0.2, 0.3, 3, 0.3, 0.2],
    [0.1, 0.2, 0.2, 2, 0.1],
];

// Sum of M_INV columns: maps Δ(target stat) to Δ(sum of bp components).
const M_INV_COL_SUM = M_BP[0].map((_, j) => M_INV.reduce((s, row) => s + row[j], 0));
const M_INV_COL_SUM_NORM2 = M_INV_COL_SUM.reduce((s, c) => s + c*c, 0);
const M_INV_ROW_NORM2 = M_INV.map(row => row.reduce((s, c) => s + c*c, 0));

// Largest-remainder rounding: round each value to integer while preserving total sum.
function _roundPreservingSum(values, totalSum) {
    const n = values.length;
    const floors = values.map(v => Math.floor(v));
    const fracs = values.map((v, i) => ({i, frac: v - floors[i]}));
    let remaining = totalSum - floors.reduce((s, v) => s + v, 0);
    fracs.sort((a, b) => b.frac - a.frac);
    const out = floors.slice();
    for (let k = 0; k < n && remaining > 0; k++) {
        out[fracs[k].i]++;
        remaining--;
    }
    for (let k = n - 1; k >= 0 && remaining < 0; k--) {
        if (out[fracs[k].i] > 0) {
            out[fracs[k].i]--;
            remaining++;
        }
    }
    return out;
}

function _matvec(Mat, v) {
    const out = new Array(Mat.length);
    for (let i = 0; i < Mat.length; i++) {
        let s = 0;
        const row = Mat[i];
        for (let j = 0; j < row.length; j++) s += row[j] * v[j];
        out[i] = s;
    }
    return out;
}

// Continuous-r feasibility: find r ∈ [0,10]^5 with sum r = 10 such that
// floor(M·(m + bprate·r))_i + 20 = target_i for all 5 axes.
// Uses cyclic projection in w = M·r space. Returns {r, x} or null.
// (BP is fractional in-game; integer enumeration of r misses solutions where
//  the unique exact-stat r is non-integer. This recovers those via LP feasibility.)
function _lpFeasibleContinuous(m, target, bprate) {
    const Mm = _matvec(M_BP, m);
    const Wlo = new Array(5);
    const Whi = new Array(5);
    for (let i = 0; i < 5; i++) {
        Wlo[i] = (target[i] - 20 - Mm[i]) / bprate;
        Whi[i] = (target[i] - 19 - Mm[i]) / bprate;
    }
    // Necessary: sum r = C·w = 10 must be achievable for w in box.
    let minSum = 0, maxSum = 0;
    for (let j = 0; j < 5; j++) {
        const c = M_INV_COL_SUM[j];
        const lo = c >= 0 ? c * Wlo[j] : c * Whi[j];
        const hi = c >= 0 ? c * Whi[j] : c * Wlo[j];
        minSum += lo;
        maxSum += hi;
    }
    if (10 < minSum - 1e-7 || 10 > maxSum + 1e-7) return null;

    function verify(w) {
        const r = _matvec(M_INV, w);
        for (let i = 0; i < 5; i++) {
            if (r[i] < -1e-6 || r[i] > 10 + 1e-6) return null;
            if (w[i] < Wlo[i] - 1e-6 || w[i] > Whi[i] + 1e-6) return null;
        }
        let s = 0;
        for (let i = 0; i < 5; i++) s += r[i];
        if (Math.abs(s - 10) > 1e-4) return null;
        // Verify exact stats via floor.
        const x = m.map((mi, i) => mi + bprate * r[i]);
        const Mx = _matvec(M_BP, x);
        for (let i = 0; i < 5; i++) {
            const stat = Math.floor(Math.round(Mx[i] * 10000) / 10000) + 20;
            if (stat !== target[i]) return null;
        }
        // Clamp tiny negatives to 0 for cleaner output.
        const rClean = r.map(v => v < 0 ? 0 : (v > 10 ? 10 : v));
        return {r: rClean, x};
    }

    function project(w0) {
        const w = w0.slice();
        for (let iter = 0; iter < 60; iter++) {
            // Project to sum r = C·w = 10.
            let sumW = 0;
            for (let i = 0; i < 5; i++) sumW += M_INV_COL_SUM[i] * w[i];
            if (Math.abs(sumW - 10) > 1e-9) {
                const k = (10 - sumW) / M_INV_COL_SUM_NORM2;
                for (let i = 0; i < 5; i++) w[i] += k * M_INV_COL_SUM[i];
            }
            // Project onto stat box.
            for (let i = 0; i < 5; i++) {
                if (w[i] < Wlo[i]) w[i] = Wlo[i];
                else if (w[i] > Whi[i] - 1e-9) w[i] = Whi[i] - 1e-9;
            }
            // Project onto r_i ∈ [0, 10].
            const r = _matvec(M_INV, w);
            for (let i = 0; i < 5; i++) {
                if (r[i] < -1e-9) {
                    const k = -r[i] / M_INV_ROW_NORM2[i];
                    for (let j = 0; j < 5; j++) w[j] += k * M_INV[i][j];
                } else if (r[i] > 10 + 1e-9) {
                    const k = (r[i] - 10) / M_INV_ROW_NORM2[i];
                    for (let j = 0; j < 5; j++) w[j] -= k * M_INV[i][j];
                }
            }
            const v = verify(w);
            if (v) return v;
        }
        return null;
    }

    // Start 1: box center.
    const wMid = new Array(5);
    for (let i = 0; i < 5; i++) wMid[i] = (Wlo[i] + Whi[i]) / 2;
    let res = project(wMid);
    if (res) return res;
    // Start 2: shift center toward sum r = 10 in w-space.
    let sumMid = 0;
    for (let i = 0; i < 5; i++) sumMid += M_INV_COL_SUM[i] * wMid[i];
    const shift = (10 - sumMid) / M_INV_COL_SUM_NORM2;
    const wShift = wMid.map((wi, i) => wi + shift * M_INV_COL_SUM[i]);
    res = project(wShift);
    if (res) return res;
    // Start 3-5: per-axis biased corners. Pick the box corner closest to sum r = 10.
    // Try the 3 corners with sum r closest to 10.
    const corners = [];
    for (let mask = 0; mask < 32; mask++) {
        const wc = new Array(5);
        let cs = 0;
        for (let i = 0; i < 5; i++) {
            wc[i] = (mask >> i) & 1 ? Whi[i] - 1e-9 : Wlo[i];
            cs += M_INV_COL_SUM[i] * wc[i];
        }
        corners.push({wc, dist: Math.abs(cs - 10)});
    }
    corners.sort((a, b) => a.dist - b.dist);
    for (let k = 0; k < 3; k++) {
        res = project(corners[k].wc);
        if (res) return res;
    }
    return null;
}

class Stat {
    constructor(lvl, hp, mp, attack, defend, agi) {
        this.lvl = lvl;
        this.hp = hp;
        this.mp = mp;
        this.attack = attack;
        this.defend = defend;
        this.agi = agi;
    }

    guessGrow(growRange, rate) {
        const hp = growRange.hpp, atk = growRange.attackp, def = growRange.defendp, agi = growRange.agip,
            mp = growRange.mpp;
        const stat = new BP(hp * rate, atk * rate, def * rate, agi * rate, mp * rate).calcRealNum();
        // stat.print();
        stat.lvl = this.lvl;
        return stat;
    }

    // 寵物所有能力由BP決定, 血魔攻防敏各有20點的基本值, 精神跟回復基本值為
    // 100點,
    //       生命 魔力 攻擊  防禦   敏捷   精神   回復
    // +體力   8   1   0.2  0.2    0.1   -0.3   0.8
    // +力量   2   2   2.7  0.3    0.2   -0.1  -0.1
    // +強度   3   2   0.3  3      0.2    0.2  -0.1
    // +速度   3   2   0.3  0.3    2     -0.1   0.2
    // +魔法   1  10   0.2  0.2    0.1    0.8  -0.3

    toBP() {
        const hp = this.hp, mp = this.mp, atk = this.attack,
            defStat = this.defend, agi = this.agi;

        const martrix = [
            [8, 2, 3, 3, 1],
            [1, 2, 2, 2, 10],
            [0.2, 2.7, 0.3, 0.3, 0.2],
            [0.2, 0.3, 3, 0.3, 0.2],
            [0.1, 0.2, 0.2, 2, 0.1],
        ];

        // 血魔攻防敏各有20點的基本值, 精神跟回復基本值 100點,
        const base = 20;
        const b = [hp - base, mp - base, atk -
        base, defStat - base, agi - base];

        // 使用 numpy-equivalent 库求解线性方程组
        const x = lusolve(martrix, b);

        return new BP(
            x[0][0],
            x[1][0],
            x[2][0],
            x[3][0],
            x[4][0],
        );
    }

    str() {
        return ["lvl:" + this.lvl +
        ",hp:", this.hp +
        ",mp:", this.mp +
        ",attack:", this.attack +
        ",defend:", this.defend +
        ",agi:", this.agi].join("");
    }

    equal(stat) {
        return this.same(stat);
    }

    toArray() {
        return [this.hp, this.attack, this.defend, this.agi, this.mp];
    }

    same(stat, tolerance = 0) {

        if (Math.abs(sum(this.toArray()) - sum(stat.toArray())) > tolerance) {
            return false;
        }

        if (calcDiff(this.toArray(), stat.toArray()).filter(n => Math.abs(n) > tolerance).length) {
            return false;
        }

        return true;

        // return this.hp == stat.hp &&
        //     this.mp == stat.mp &&
        //     this.attack == stat.attack &&
        //     this.defend == stat.defend &&
        //     this.agi == stat.agi
    }
}

class BP {
    constructor(hp, attack, defend, agi, mp) {
        this.hpp = hp;
        this.mpp = mp;
        this.attackp = attack;
        this.defendp = defend;
        this.agip = agi;
    }

    // 寵物所有能力由BP決定, 血魔攻防敏各有20點的基本值, 精神跟回復基本值為
    // 100點,
    //       生命 魔力 攻擊  防禦   敏捷   精神   回復
    // +體力   8   1   0.2  0.2    0.1   -0.3   0.8
    // +力量   2   2   2.7  0.3    0.2   -0.1  -0.1
    // +強度   3   2   0.3  3      0.2    0.2  -0.1
    // +速度   3   2   0.3  0.3    2     -0.1   0.2
    // +魔法   1  10   0.2  0.2    0.1    0.8  -0.3
    calcHP() {
        const martrix = [8, 2, 3, 3, 1];
        return this.hpp * martrix[0] + this.attackp * martrix[1] +
            +this.defendp * martrix[2] + this.agip * martrix[3] + this.mpp * martrix[4];
    }

    calcMP() {
        const martrix = [1, 2, 2, 2, 10];
        return this.hpp * martrix[0] + this.attackp * martrix[1] +
            +this.defendp * martrix[2] + this.agip * martrix[3] + this.mpp * martrix[4];
    }

    toArray() {
        return [this.hpp, this.attackp, this.defendp, this.agip, this.mpp];
    }

    calcATK() {
        const martrix = [0.2, 2.7, 0.3, 0.3, 0.2];
        return this.hpp * martrix[0] + this.attackp * martrix[1] +
            +this.defendp * martrix[2] + this.agip * martrix[3] + this.mpp * martrix[4];
    }


    calcDEF() {
        const martrix = [0.2, 0.3, 3, 0.3, 0.2];
        return this.hpp * martrix[0] + this.attackp * martrix[1] +
            +this.defendp * martrix[2] + this.agip * martrix[3] + this.mpp * martrix[4];
    }

    calcAGI() {
        const martrix = [0.1, 0.2, 0.2, 2, 0.1];
        return this.hpp * martrix[0] + this.attackp * martrix[1] +
            +this.defendp * martrix[2] + this.agip * martrix[3] + this.mpp * martrix[4];
    }

    calcWIS() {
        const martrix = [-0.3, -0.1, 0.2, -0.1, 0.8];
        return this.hpp * martrix[0] + this.attackp * martrix[1] +
            +this.defendp * martrix[2] + this.agip * martrix[3] + this.mpp * martrix[4];
    }

    calcRes() {
        const martrix = [0.8, -0.1, -0.1, 0.2, -0.3,];
        return this.hpp * martrix[0] + this.attackp * martrix[1] +
            +this.defendp * martrix[2] + this.agip * martrix[3] + this.mpp * martrix[4];
    }

    contains(anotherBP) {
        return this.hpp <= anotherBP.hpp
            && this.mpp <= anotherBP.mpp
            && this.attackp <= anotherBP.attackp
            && this.defendp <= anotherBP.defendp
            && this.agip <= anotherBP.agip;
    }

    sum() {
        return this.hpp
            + this.mpp
            + this.attackp
            + this.defendp
            + this.agip;
    }

    calcRealNum() {
        const propBase = 20;

        const fixPos = (n) => {
            return Math.floor(Math.round(n * 10000) / 10000);
        }
        const s = new Stat(0, ...[
            fixPos(this.calcHP()) + propBase,
            fixPos(this.calcMP()) + propBase,
            fixPos(this.calcATK()) + propBase,
            fixPos(this.calcDEF()) + propBase,
            fixPos(this.calcAGI()) + propBase,
            fixPos(this.calcWIS()) + 100,
            fixPos(this.calcRes()) + 100
        ]);//.map(n=> Math.floor(n)));

        return s;
    }

    str() {
        return ("hp:", this.hpp +
        ",mp:", this.mpp +
        ",attack:", this.attackp +
        ",defend:", this.defendp +
        ",agi:", this.agip);
    }

}


// 家寵
// 總BP =  GrowSum*rate + 2 (隨機) + (n-1)*seed + (n-1)

// 野寵
// 總BP =

class GrowRange {

    constructor(hp, attack, defend, agi, mp, bprate) {
        this.hpp = parseFloat(hp);
        this.mpp = parseFloat(mp);
        this.attackp = parseFloat(attack);
        this.defendp = parseFloat(defend);
        this.agip = parseFloat(agi);
        if (bprate == null) {
            this.bprate = 0.2;
        } else {
            this.bprate = bprate;
        }
    }

    contains(anotherGrow) {
        return this.hpp <= anotherGrow.hpp
            && this.mpp <= anotherGrow.mpp
            && this.attackp <= anotherGrow.attackp
            && this.defendp <= anotherGrow.defendp
            && this.agip <= anotherGrow.agip;
    }

    drop(hpp, atkp, defp, agip, mpp) {
        return new GrowRange(this.hpp - Math.abs(hpp), this.attackp - Math.abs(atkp),
            this.defendp - Math.abs(defp), this.agip - Math.abs(agip),
            this.mpp - Math.abs(mpp), this.bprate);

    }

    same(agw) {
        return this.hpp == agw.hpp
            && this.mpp == agw.mpp
            && this.attackp == agw.attackp
            && this.defendp == agw.defendp
            && this.agip == agw.agip;

    }

    toArray() {
        return [this.hpp, this.attackp, this.defendp, this.agip, this.mpp];
    }


    sum() {
        return this.hpp
            + this.mpp
            + this.attackp
            + this.defendp
            + this.agip;
    }

    calcBPAtLevel(lvl, lvlpoint) {

        const bps = [
            this.hpp * this.bprate,
            this.attackp * this.bprate,
            this.defendp * this.bprate,
            this.agip * this.bprate,
            this.mpp * this.bprate,
        ];

        const lvldiff = lvl - 1;

        const shift = 0;
        bps[0] = bps[0] + (fullRates[this.hpp - shift] * lvldiff);
        bps[1] = bps[1] + (fullRates[this.attackp - shift] * lvldiff);
        bps[2] = bps[2] + (fullRates[this.defendp - shift] * lvldiff);
        bps[3] = bps[3] + (fullRates[this.agip - shift] * lvldiff);
        bps[4] = bps[4] + (fullRates[this.mpp - shift] * lvldiff);

        if (lvlpoint == null) {
            lvlpoint = lvldiff;
        }

        return {
            baseBP: new BP(...bps),
            sumBaseBP: sum(bps) + (10 * this.bprate),
            sumFullBP: sum(bps) + (10 * this.bprate) + lvlpoint
        };

    }

    mockLoopRange(grow, cb) {
        cb(sum(this.bps()), grow);

    }

    loopRange(cb) {
        const sumBP = sum(this.bps())
        // catalog this.X is the upper bound — values above always fail `growRange.contains(this)` anyway.
        // Max drop per axis is 4, so lower bound is this.X - 4.
        const v1 = [this.hpp - 4, this.hpp];
        const v2 = [this.attackp - 4, this.attackp];
        const v3 = [this.defendp - 4, this.defendp];
        const v4 = [this.agip - 4, this.agip];
        const v5 = [this.mpp - 4, this.mpp];

        for (var a = v1[0]; a <= v1[1]; a++) {
            for (var b = v2[0]; b <= v2[1]; b++) {
                for (var c = v3[0]; c <= v3[1]; c++) {
                    for (var d = v4[0]; d <= v4[1]; d++) {
                        for (var e = v5[0]; e <= v5[1]; e++) {
                            cb(sumBP, new GrowRange(a, b, c, d, e, this.bprate));
                        }
                    }
                }
            }
        }
    }

    bps() {
        return [this.hpp, this.attackp, this.defendp, this.agip, this.mpp];
    }

    guess(stat, notorderpoint = 0, targetGrow = null) {
        let res = this.guessWithSpecficLvlPoint(stat, stat.lvl - 1 - notorderpoint, targetGrow);

        if (res.length == 0 && stat.lvl != 1) {
            res = this.guessWithSpecficLvlPoint(stat, 0, targetGrow);
        }

        // Continuous-r fallback: when integer enumeration finds nothing, the exact-stat r
        // may simply be non-integer. Run LP feasibility per (gr, manual) candidate.
        if (res.length == 0 && stat.lvl != 1) {
            res = this.guessWithSpecficLvlPointContinuous(stat, stat.lvl - 1 - notorderpoint, targetGrow);
        }

        return res;
    }


    guessWithSpecficLvlPoint(stat, point, targetGrow) {
        const result = [];

        const calcBP = stat.toBP();

        const statUp = new Stat(stat.lvl, stat.hp + 1, stat.mp + 1, stat.attack + 1,
            stat.defend + 1, stat.agi + 1);
        const calcUpBp = statUp.toBP();

        const oSum = calcBP.sum();
        const oUpSum = calcUpBp.sum();

        const results = [];

        if (targetGrow) {
            this.mockLoopRange(this.drop(...targetGrow.toArray()), (sumBP, growRange) => {
                return this._handleGuessingGrowRange(growRange, stat, point, oSum,
                    oUpSum, calcUpBp, results, result, sumBP);
            })
            return result;
        }
        // this.mockLoopRange(this.drop(2, 1, 0, 1, 0), (sumBP, growRange) => {
        this.loopRange((sumBP, growRange) => {
            return this._handleGuessingGrowRange(growRange, stat, point, oSum,
                oUpSum, calcUpBp, results, result, sumBP);
        })

        return result;
    }


    guessWithSpecficLvlPointContinuous(stat, point, targetGrow) {
        const result = [];
        const calcBP = stat.toBP();
        const statUp = new Stat(stat.lvl, stat.hp + 1, stat.mp + 1, stat.attack + 1,
            stat.defend + 1, stat.agi + 1);
        const calcUpBp = statUp.toBP();
        const oSum = calcBP.sum();
        const oUpSum = calcUpBp.sum();

        if (targetGrow) {
            this.mockLoopRange(this.drop(...targetGrow.toArray()), (sumBP, growRange) => {
                this._handleContinuousGrowRange(growRange, stat, point, oSum, oUpSum,
                    calcUpBp, result, sumBP);
            });
            return result;
        }
        this.loopRange((sumBP, growRange) => {
            this._handleContinuousGrowRange(growRange, stat, point, oSum, oUpSum,
                calcUpBp, result, sumBP);
        });
        return result;
    }


    _handleContinuousGrowRange(growRange, stat, point, oSum, oUpSum, calcUpBp, result, sumBP) {
        if (!growRange.contains(this)) return false;
        const res = growRange.calcBPAtLevel(stat.lvl, point);
        if (!(res.sumFullBP >= oSum && res.sumFullBP <= oUpSum)) return;

        const baseArr = res.baseBP.toArray();
        const upArr = calcUpBp.toArray();
        const sl0 = upArr[0] - baseArr[0] + 1;
        const sl1 = upArr[1] - baseArr[1] + 1;
        const sl2 = upArr[2] - baseArr[2] + 1;
        const sl3 = upArr[3] - baseArr[3] + 1;
        const sl4 = upArr[4] - baseArr[4] + 1;

        const bps0 = baseArr[0], bps1 = baseArr[1], bps2 = baseArr[2], bps3 = baseArr[3], bps4 = baseArr[4];
        const bprate = growRange.bprate;
        const target = [stat.hp, stat.mp, stat.attack, stat.defend, stat.agi];
        const maxBPs = this.bps();
        const possibleLost = possibleLostRange(growRange, maxBPs);
        const grSum = growRange.sum();

        const aMax = Math.min(sl0, point);
        for (let a = 0; a <= aMax; a++) {
            const remA = point - a;
            const bMax = Math.min(sl1, remA);
            for (let b = 0; b <= bMax; b++) {
                const remB = remA - b;
                const cMax = Math.min(sl2, remB);
                for (let c = 0; c <= cMax; c++) {
                    const remC = remB - c;
                    const dMax = Math.min(sl3, remC);
                    for (let d = 0; d <= dMax; d++) {
                        const e = remC - d;
                        if (e < 0 || e > sl4) continue;
                        const m = [bps0 + a, bps1 + b, bps2 + c, bps3 + d, bps4 + e];
                        const lp = _lpFeasibleContinuous(m, target, bprate);
                        if (!lp) continue;
                        const bp = new BP(lp.x[0], lp.x[1], lp.x[2], lp.x[3], lp.x[4]);
                        const calcState = bp.calcRealNum();
                        const rInt = _roundPreservingSum(lp.r, 10);
                        result.push({
                            SumGrowBPs: sumBP,
                            MaxGrowBPs: maxBPs,
                            GuessRange: growRange,
                            LostBP: grSum - sumBP,
                            PossibleLost: possibleLost,
                            guess: calcState,
                            ManualPoints: [a, b, c, d, e],
                            RandomRange: rInt,
                            RandomRangeFloat: lp.r,
                            isApproximate: true,
                        });
                    }
                }
            }
        }
    }


    _handleGuessingGrowRange(growRange, stat, point, oSum, oUpSum, calcUpBp, results, result, sumBP) {
        if (!growRange.contains(this)) {
            return false;
        }
        const res = growRange.calcBPAtLevel(stat.lvl, point);

        if (!(res.sumFullBP >= oSum && res.sumFullBP <= oUpSum)) return;

        // softLimit per axis: how much manual point can be added without exceeding stat-up bp
        const baseArr = res.baseBP.toArray();
        const upArr = calcUpBp.toArray();
        const sl0 = upArr[0] - baseArr[0] + 1;
        const sl1 = upArr[1] - baseArr[1] + 1;
        const sl2 = upArr[2] - baseArr[2] + 1;
        const sl3 = upArr[3] - baseArr[3] + 1;
        const sl4 = upArr[4] - baseArr[4] + 1;

        const bps0 = baseArr[0], bps1 = baseArr[1], bps2 = baseArr[2], bps3 = baseArr[3], bps4 = baseArr[4];
        const bprate = growRange.bprate;
        const tHp = stat.hp, tMp = stat.mp, tAtk = stat.attack, tDef = stat.defend, tAgi = stat.agi;

        // Random-contribution bounds: r tuple has sum=10, each in [0,10].
        // For coefficient row, min(c·r) = min(c)*10, max(c·r) = max(c)*10.
        const minHpR = bprate * 10, maxHpR = bprate * 80;
        const minMpR = bprate * 10, maxMpR = bprate * 100;
        const minAtkR = bprate * 2, maxAtkR = bprate * 27;
        const minDefR = bprate * 2, maxDefR = bprate * 30;
        const minAgiR = bprate * 1, maxAgiR = bprate * 20;

        const maxBPs = this.bps();
        const possibleLost = possibleLostRange(growRange, maxBPs);
        const grSum = growRange.sum();

        // Walk (a,b,c,d,e) summing to `point`, each ≤ corresponding softLimit.
        // Inlined from loopForSum to avoid recursion + array allocation overhead.
        const aMax = Math.min(sl0, point);
        for (let a = 0; a <= aMax; a++) {
            const m0 = bps0 + a;
            const remA = point - a;
            const bMax = Math.min(sl1, remA);
            for (let b = 0; b <= bMax; b++) {
                const m1 = bps1 + b;
                const remB = remA - b;
                const cMax = Math.min(sl2, remB);
                for (let c = 0; c <= cMax; c++) {
                    const m2 = bps2 + c;
                    const remC = remB - c;
                    const dMax = Math.min(sl3, remC);
                    for (let d = 0; d <= dMax; d++) {
                        const m3 = bps3 + d;
                        const e = remC - d;
                        if (e < 0 || e > sl4) continue;
                        const m4 = bps4 + e;

                        // Prune: skip if no random tuple can fill the gap to target.
                        const hpBase = 8*m0 + 2*m1 + 3*m2 + 3*m3 + m4;
                        if (tHp - 19 - hpBase <= minHpR || tHp - 20 - hpBase >= maxHpR) continue;
                        const mpBase = m0 + 2*m1 + 2*m2 + 2*m3 + 10*m4;
                        if (tMp - 19 - mpBase <= minMpR || tMp - 20 - mpBase >= maxMpR) continue;
                        const atkBase = 0.2*m0 + 2.7*m1 + 0.3*m2 + 0.3*m3 + 0.2*m4;
                        if (tAtk - 19 - atkBase <= minAtkR || tAtk - 20 - atkBase >= maxAtkR) continue;
                        const defBase = 0.2*m0 + 0.3*m1 + 3*m2 + 0.3*m3 + 0.2*m4;
                        if (tDef - 19 - defBase <= minDefR || tDef - 20 - defBase >= maxDefR) continue;
                        const agiBase = 0.1*m0 + 0.2*m1 + 0.2*m2 + 2*m3 + 0.1*m4;
                        if (tAgi - 19 - agiBase <= minAgiR || tAgi - 20 - agiBase >= maxAgiR) continue;

                        // Algebraic estimate: r ≈ M_INV · (target - 19.5 - base) / bprate.
                        // Then enumerate ±1 ball (M_INV worst-case row projection ~2.6 covers integer offsets).
                        const dHp = (tHp - 19.5 - hpBase) / bprate;
                        const dMp = (tMp - 19.5 - mpBase) / bprate;
                        const dAtk = (tAtk - 19.5 - atkBase) / bprate;
                        const dDef = (tDef - 19.5 - defBase) / bprate;
                        const dAgi = (tAgi - 19.5 - agiBase) / bprate;

                        const r0c = Math.round(M_INV[0][0]*dHp + M_INV[0][1]*dMp + M_INV[0][2]*dAtk + M_INV[0][3]*dDef + M_INV[0][4]*dAgi);
                        const r1c = Math.round(M_INV[1][0]*dHp + M_INV[1][1]*dMp + M_INV[1][2]*dAtk + M_INV[1][3]*dDef + M_INV[1][4]*dAgi);
                        const r2c = Math.round(M_INV[2][0]*dHp + M_INV[2][1]*dMp + M_INV[2][2]*dAtk + M_INV[2][3]*dDef + M_INV[2][4]*dAgi);
                        const r3c = Math.round(M_INV[3][0]*dHp + M_INV[3][1]*dMp + M_INV[3][2]*dAtk + M_INV[3][3]*dDef + M_INV[3][4]*dAgi);

                        for (let dr0 = -1; dr0 <= 1; dr0++) {
                            const r0 = r0c + dr0;
                            if (r0 < 0 || r0 > 10) continue;
                            const x0 = m0 + bprate * r0;
                            for (let dr1 = -1; dr1 <= 1; dr1++) {
                                const r1 = r1c + dr1;
                                if (r1 < 0 || r1 > 10) continue;
                                const x1 = m1 + bprate * r1;
                                for (let dr2 = -1; dr2 <= 1; dr2++) {
                                    const r2 = r2c + dr2;
                                    if (r2 < 0 || r2 > 10) continue;
                                    const x2 = m2 + bprate * r2;
                                    for (let dr3 = -1; dr3 <= 1; dr3++) {
                                        const r3 = r3c + dr3;
                                        if (r3 < 0 || r3 > 10) continue;
                                        const r4 = 10 - r0 - r1 - r2 - r3;
                                        if (r4 < 0 || r4 > 10) continue;
                                        const x3 = m3 + bprate * r3;
                                        const x4 = m4 + bprate * r4;

                                        const hp = Math.floor(Math.round((8*x0 + 2*x1 + 3*x2 + 3*x3 + x4) * 10000) / 10000) + 20;
                                        if (hp !== tHp) continue;
                                        const mp = Math.floor(Math.round((x0 + 2*x1 + 2*x2 + 2*x3 + 10*x4) * 10000) / 10000) + 20;
                                        if (mp !== tMp) continue;
                                        const atk = Math.floor(Math.round((0.2*x0 + 2.7*x1 + 0.3*x2 + 0.3*x3 + 0.2*x4) * 10000) / 10000) + 20;
                                        if (atk !== tAtk) continue;
                                        const def = Math.floor(Math.round((0.2*x0 + 0.3*x1 + 3*x2 + 0.3*x3 + 0.2*x4) * 10000) / 10000) + 20;
                                        if (def !== tDef) continue;
                                        const agi = Math.floor(Math.round((0.1*x0 + 0.2*x1 + 0.2*x2 + 2*x3 + 0.1*x4) * 10000) / 10000) + 20;
                                        if (agi !== tAgi) continue;

                                        const bp = new BP(x0, x1, x2, x3, x4);
                                        const calcState = bp.calcRealNum();
                                        result.push({
                                            SumGrowBPs: sumBP,
                                            MaxGrowBPs: maxBPs,
                                            GuessRange: growRange,
                                            LostBP: grSum - sumBP,
                                            PossibleLost: possibleLost,
                                            guess: calcState,
                                            ManualPoints: [a, b, c, d, e],
                                            RandomRange: [r0, r1, r2, r3, r4]
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }


}


function possibleLostRange(growRange, maxBP) {
    const maxBasePos = 10;

    const sureLost = [];
    const guessRange = growRange.toArray();
    for (var i = 0; i < guessRange.length; ++i) {
        if (guessRange[i] < maxBP[i]) {
            sureLost[i] = maxBP[i] - guessRange[i];
        } else {
            sureLost[i] = 0;
        }
    }
    const sumSureLost = sum(sureLost);

    const sureBaseOver = [];
    for (var i = 0; i < guessRange.length; ++i) {
        if (guessRange[i] > maxBP[i]) {
            sureBaseOver[i] = guessRange[i] - maxBP[i];
        } else {
            sureBaseOver[i] = 0;
        }
    }
    let sumSureBase = sum(sureBaseOver);

    const possibleLostRange = [];
    for (var i = 0; i < guessRange.length; ++i) {
        const min = maxBP[i] - 5;
        let max = maxBP[i];
        const thisoverBase = guessRange[i] - maxBP[i];
        const otherOverbase = sumSureBase - thisoverBase;
        let localMax = maxBasePos - otherOverbase;
        possibleLostRange[i] = [
            Math.max(0, max - guessRange[i]),
            Math.min(4, max + localMax - guessRange[i])];
    }


    // console.log("穩掉", sumSureLost, "分布", sureLost);
    // console.log("基本檔穩超過", sumSureBase, "分布", sureBaseOver);
    // console.log("可能掉檔分布", possibleLostRange.map(n => n[0] + "~" + n[1]));

    return {
        sumSureLost, sureLost,
        possibleLostRange: possibleLostRange.map(n => n[0] + "~" + n[1])
    }
}

function RealGuessRaw(Pts,input) {
    const token = input.trim().split(/ /);
    return RealGuess(Pts,token[0], ...token.slice(1).map(n => parseInt(n)));
}

function RealGuess(Pts,name, lvl, hp, mp, attack, def, agi, notorderpoint,targetGrow) {
    const pet = Pts.filter(n => n[1] == name)[0];
    if (pet == null) {
        return {pet: {name: name, find: false, lvl: lvl}};
    }


    const bps = [pet[3], pet[4], pet[5], pet[6], pet[7]];
    try {
        const bprate = pet[8] == null ? 0.2 : parseFloat(pet[8]);
        const rng = new GrowRange(...bps, bprate);

        const stat = new Stat(lvl, hp, mp, attack, def, agi);
        const results = rng.guess(stat,notorderpoint, targetGrow);

        return {pet: {name: pet[1], find: true, lvl: lvl}, bps, results};
    } catch (err) {
        console.log(err);
        throw err;
    }
}

const sumArray = sum;
export {RealGuess, RealGuessRaw, BP, Stat, GrowRange, sumArray,  calcDiff, minmax, GuessResultToString};
