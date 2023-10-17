'use strict'


import {RealGuess, GuessResultToString, PetDefaultData} from "../index.js"
import assert from 'assert'

describe('app.all()', function () {

    it("純白液態史萊姆 59 1815 701 280 189 140 13", (done) => {
        var testcase = "純白液態史萊姆 59 1815 701 280 189 140 13";
        console.log("輸入資料:" + testcase);
        const token = testcase.split(/ /).filter(n => n != "");

        const params = token.slice(1).map(n => parseInt(n));
        const lvl = params.length == 5 ? 1 : params[0];
        const otherparams = params.length == 5 ? params : params.slice(1);
        const results = RealGuess(PetDefaultData, token[0], lvl,
            ...otherparams
        );
        const limit = 10;
        const showDetails = 100;

        console.log(GuessResultToString(results, limit, showDetails));

        assert.strictEqual(59, results.pet.lvl);
        done();

    });
});
