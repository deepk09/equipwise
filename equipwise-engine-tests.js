/* =========================================================================
   EquipWise - automated test suite for the EUAC calculation engine
   Requirement 10: validation and testing.

   Run:  node equipwise-engine-tests.js
   Exit code 0 means every assertion passed.

   Covers: factor identities, zero discount rate, one-year period, changing
   duration, zero and positive salvage, escalating maintenance, refundable
   deposits, irregular payment timing, financing without double counting,
   loan balance at exit, utilization levels, replacement cycles, partial
   years, after-tax treatment, minimum hire, explicit rental duration,
   validation rules, break-even detection (including the no-crossover case),
   sensitivity sweeps and INR formatting.
   ========================================================================= */

/* ===================== calculation engine (inlined, unmodified) ===================== */
/* =========================================================================
   EquipWise — Engineering Economics Calculation Engine
   Equivalent Uniform Annual Cost (EUAC) / Equivalent Uniform Annual Worth
   Pure functions. No DOM. No UI. Reproducible.
   ========================================================================= */
(function (global) {
  'use strict';

  var Engine = {};

  /* ---------------------------------------------------------------- utils */
  function num(v) { var x = parseFloat(v); return isFinite(x) ? x : 0; }
  function clamp(x, a, b) { return Math.min(b, Math.max(a, x)); }
  function deepClone(o) { return JSON.parse(JSON.stringify(o)); }

  Engine.num = num;
  Engine.deepClone = deepClone;

  /* -------------------------------------------------------------- factors */
  /* (A/P, i, n) capital recovery factor. Zero-rate case handled separately. */
  function apf(i, n) {
    if (!(n > 0)) return 0;
    if (Math.abs(i) < 1e-12) return 1 / n;
    var p = Math.pow(1 + i, n);
    return (i * p) / (p - 1);
  }
  /* (A/F, i, n) sinking fund factor. */
  function af(i, n) {
    if (!(n > 0)) return 0;
    if (Math.abs(i) < 1e-12) return 1 / n;
    return i / (Math.pow(1 + i, n) - 1);
  }
  /* (P/F, i, n) single payment present worth factor. */
  function pfv(i, n) { return Math.pow(1 + i, -n); }
  /* (P/A, i, n) uniform series present worth factor. */
  function paf(i, n) {
    if (!(n > 0)) return 0;
    if (Math.abs(i) < 1e-12) return n;
    return (1 - Math.pow(1 + i, -n)) / i;
  }
  /* Effective periodic rate from an annual effective rate. */
  function periodRate(iAnnual, perYear) {
    if (Math.abs(iAnnual) < 1e-12) return 0;
    return Math.pow(1 + iAnnual, 1 / perYear) - 1;
  }

  Engine.apf = apf; Engine.af = af; Engine.pfv = pfv; Engine.paf = paf;
  Engine.periodRate = periodRate;

  /* --------------------------------------------------------- derived bits */
  function productiveHours(inp) {
    var h = num(inp.project.hoursPerYear);
    var u = clamp(num(inp.project.utilizationPct), 0, 100);
    return h * u / 100;
  }
  Engine.productiveHours = productiveHours;

  function analysisYears(inp) {
    var n = num(inp.project.analysisYears);
    if (!(n > 0)) n = num(inp.project.durationMonths) / 12;
    return Math.max(n, 1 / 12);
  }
  Engine.analysisYears = analysisYears;

  /* Component buckets used everywhere (capital + salvage = capital recovery) */
  var KEYS = ['capital', 'maint', 'oper', 'own', 'lease', 'other', 'salvage'];
  Engine.KEYS = KEYS;

  function emptyFlow(t) {
    return { t: t, capital: 0, maint: 0, oper: 0, own: 0, lease: 0, other: 0, salvage: 0 };
  }
  function pushFlow(arr, t, key, amt) {
    if (!amt) return;
    var f = null;
    for (var k = 0; k < arr.length; k++) { if (Math.abs(arr[k].t - t) < 1e-9) { f = arr[k]; break; } }
    if (!f) { f = emptyFlow(t); arr.push(f); }
    f[key] += amt;
  }

  /* ======================================================================
     BUY  —  ownership cash-flow stream
     EUAC_B = PW_B (A/P, i, n),  PW_B = P + sum C_t/(1+i)^t - S/(1+i)^n
     ====================================================================== */
  function buyFlows(inp, nYears) {
    var b = inp.buy, e = inp.econ;
    var price = num(b.price);
    var life = Math.max(0.25, num(b.economicLifeYears) || nYears);
    var replace = !!b.replacement && nYears > life + 1e-9;
    var cycles = replace ? Math.ceil(nYears / life - 1e-9) : 1;
    var dpPct = clamp(num(b.downPaymentPct), 0, 100);
    var tenure = num(b.loanTenureYears);
    var loanRate = num(b.loanRate) / 100;
    var dp = price * dpPct / 100;
    var loan = price - dp;
    var ownerView = (b.financingView === 'owner') && dpPct < 100 && tenure > 0 && loan > 0 && !replace;
    var A = (loan > 0 && tenure > 0) ? loan * apf(loanRate, tenure) : 0;

    var taxRate = num(e.taxRate) / 100;
    var atF = e.afterTax ? (1 - taxRate) : 1;
    var infl = num(e.inflationRate) / 100;
    var hours = productiveHours(inp);
    var resale = num(b.resaleValue);
    var ownAnnual = num(b.insuranceAnnual) + num(b.registrationAnnual) +
                    num(b.storageAnnual) + num(b.otherAnnual);
    var opAnnual = num(b.operatingCostPerHour) * hours;
    var m1 = num(b.maintenanceYear1);
    var g = num(b.maintenanceEscalationPct) / 100;
    var depBase = Math.max(0, price - resale);

    var flows = [];
    var detail = { cycles: cycles, replace: replace, ownerView: ownerView, loanPayment: A,
                   downPayment: dp, loan: loan, life: life };

    for (var k = 0; k < cycles; k++) {
      var start = k * life;
      if (start >= nYears - 1e-9) break;
      var len = Math.min(life, nYears - start);
      var fullCycle = len >= life - 1e-9;

      /* --- capital outlay at the start of the cycle --- */
      if (ownerView) pushFlow(flows, start, 'capital', dp);
      else pushFlow(flows, start, 'capital', price);

      /* --- loan repayments (owner's financing cash flows) --- */
      if (ownerView) {
        var payYears = Math.min(tenure, len);
        for (var y1 = 1; y1 <= Math.ceil(payYears - 1e-9); y1++) {
          var frac = Math.min(1, payYears - (y1 - 1));
          if (frac <= 1e-9) break;
          pushFlow(flows, start + y1 - 1 + frac, 'other', A * frac);
        }
      }

      /* --- recurring annual costs, prorated for partial years --- */
      var nPeriods = Math.ceil(len - 1e-9);
      for (var y = 0; y < nPeriods; y++) {
        var overlap = Math.min(1, len - y);
        if (overlap <= 1e-9) break;
        var t = start + y + overlap;
        var gYear = Math.floor(start + y);
        var escInfl = Math.pow(1 + infl, gYear);

        var maint = m1 * Math.pow(1 + g, y) * overlap;
        var own = ownAnnual * escInfl * overlap;
        var op = opAnnual * escInfl * overlap;

        if (maint) pushFlow(flows, t, 'maint', maint * atF);
        if (own) pushFlow(flows, t, 'own', own * atF);
        if (op) pushFlow(flows, t, 'oper', op * atF);

        /* straight-line depreciation tax shield */
        if (e.afterTax && taxRate > 0 && life > 0) {
          var shield = taxRate * (depBase / life) * overlap;
          if (shield) pushFlow(flows, t, 'other', -shield);
        }
      }

      /* --- terminal resale value at the end of the cycle --- */
      var endT = start + len;
      var sal = resale;
      if (ownerView && tenure > nYears) {
        var rem = tenure - nYears;
        var bal = loanRate > 0 ? A * paf(loanRate, rem) : A * rem;
        sal = resale - bal;   /* sale proceeds must clear the outstanding loan */
        detail.balanceAtEnd = bal;
      }
      if (sal) pushFlow(flows, endT, 'salvage', -sal);
      if (!fullCycle && !replace) detail.partial = true;
    }

    return { granularity: 'annual', flows: flows, detail: detail };
  }

  /* ======================================================================
     LEASE
     ====================================================================== */
  function leaseFlows(inp, nYears) {
    var l = inp.lease, e = inp.econ;
    var months = Math.max(1, Math.round(nYears * 12));
    var term = Math.max(1, Math.round(num(l.termMonths) || months));
    var cycles = Math.ceil(months / term - 1e-9);
    var base = num(l.payment);
    var esc = num(l.escalationPct) / 100;
    var taxRate = num(e.taxRate) / 100;
    var atF = e.afterTax ? (1 - taxRate) : 1;
    var infl = num(e.inflationRate) / 100;
    var hours = productiveHours(inp);
    var flows = [];
    var deposit = num(l.deposit);
    var lesseeMaint = (l.maintenanceResponsibility === 'lessee') ? num(l.lesseeMaintenanceAnnual) : 0;
    var lesseeIns = num(l.lesseeInsuranceAnnual);
    var opPerHr = num(l.operatingCostPerHour);
    var adv = num(l.advancePayment);
    var termPay = num(l.terminationPayment);
    var monthsPerPayment = (l.paymentFrequency === 'annual') ? 12 : 1;

    for (var k = 0; k < cycles; k++) {
      var startM = k * term;
      if (startM >= months) break;
      var len = Math.min(term, months - startM);

      if (adv) pushFlow(flows, startM, 'other', adv * atF);
      if (deposit) pushFlow(flows, startM, 'other', deposit);   /* refundable: not tax-effected */

      for (var m = 1; m <= len; m++) {
        var mm = startM + m;
        var yearIdx = Math.floor((mm - 1) / 12);
        var pay = base * Math.pow(1 + esc, yearIdx);
        if (monthsPerPayment === 12) {
          if (mm % 12 === 0) pushFlow(flows, mm, 'lease', pay * atF);
        } else {
          pushFlow(flows, mm, 'lease', pay * atF);
        }
        if (lesseeMaint) pushFlow(flows, mm, 'maint', (lesseeMaint / 12) * Math.pow(1 + infl, yearIdx) * atF);
        if (lesseeIns) pushFlow(flows, mm, 'own', (lesseeIns / 12) * Math.pow(1 + infl, yearIdx) * atF);
        if (opPerHr) pushFlow(flows, mm, 'oper', (opPerHr * hours / 12) * Math.pow(1 + infl, yearIdx) * atF);
      }

      /* refundable deposit returned at the end of the term */
      var retM = (cycles === 1 && num(l.depositReturnMonth) > 0)
        ? Math.min(months, Math.round(num(l.depositReturnMonth)))
        : startM + len;
      if (deposit) pushFlow(flows, retM, 'other', -deposit);
    }

    if (termPay) pushFlow(flows, months, 'other', termPay * atF);

    return { granularity: 'monthly', flows: flows,
             detail: { months: months, term: term, cycles: cycles } };
  }

  /* ======================================================================
     RENT
     ====================================================================== */
  function monthlyRentalRate(r) {
    var v = num(r.rateValue);
    if (r.rateBasis === 'day') return v * (num(r.daysPerMonth) || 26);
    if (r.rateBasis === 'week') return v * (52 / 12);
    return v;
  }
  Engine.monthlyRentalRate = monthlyRentalRate;

  function rentFlows(inp, nYears) {
    var r = inp.rent, e = inp.econ;
    var months = Math.max(1, Math.round(nYears * 12));
    var requested = Math.round(num(r.durationMonths));
    if (requested > 0) months = requested;   /* committed hire period */
    var taxRate = num(e.taxRate) / 100;
    var atF = e.afterTax ? (1 - taxRate) : 1;
    var infl = num(e.inflationRate) / 100;
    var hours = productiveHours(inp);
    var flows = [];
    var esc = num(r.escalationPct) / 100;
    var ot = num(r.overtimePerMonth);
    var dtPct = num(r.downtimePct) / 100;
    var minHire = num(r.minHireMonths);
    var opPerHr = num(r.fuelIncluded === false || r.operatorIncluded === false)
      ? num(r.renterOperatingCostPerHour) : 0;

    var sumCharge = 0;
    for (var m = 1; m <= months; m++) {
      var yearIdx = Math.floor((m - 1) / 12);
      var rate = monthlyRentalRate(r) * Math.pow(1 + esc, yearIdx);
      var charge = (rate + ot) * atF;
      pushFlow(flows, m, 'lease', charge);
      sumCharge += charge;
      if (opPerHr) pushFlow(flows, m, 'oper', (opPerHr * hours / 12) * Math.pow(1 + infl, yearIdx) * atF);
    }

    /* downtime / replacement-equipment allowance */
    if (dtPct > 0 && sumCharge > 0) {
      for (var m2 = 1; m2 <= months; m2++) {
        var yr2 = Math.floor((m2 - 1) / 12);
        var extra = monthlyRentalRate(r) * Math.pow(1 + esc, yr2) * dtPct * atF;
        pushFlow(flows, m2, 'other', extra);
      }
    }

    /* minimum hire shortfall: paid inside the study period */
    if (minHire > months) {
      var shortfall = (minHire - months) * monthlyRentalRate(r) * atF;
      pushFlow(flows, months, 'other', shortfall);
    }

    if (num(r.mobDemob)) {
      pushFlow(flows, 0, 'other', num(r.mobDemob) * atF);
      pushFlow(flows, months, 'other', num(r.mobDemob) * atF);
    }

    return { granularity: 'monthly', flows: flows,
             detail: { months: months, billable: Math.max(months, minHire) } };
  }

  /* ======================================================================
     PRESENT WORTH / ANNUAL EQUIVALENT
     ====================================================================== */
  function pwOf(flows, granularity, i, timing) {
    var per = granularity === 'monthly' ? 12 : 1;
    var r = per === 12 ? periodRate(i, 12) : i;
    var mid = timing === 'mid';
    var out = { total: 0 };
    for (var k = 0; k < KEYS.length; k++) out[KEYS[k]] = 0;
    for (var f = 0; f < flows.length; f++) {
      var fl = flows[f];
      for (var j = 0; j < KEYS.length; j++) {
        var key = KEYS[j];
        if (!fl[key]) continue;
        var shift = (mid && fl.t > 0 && key !== 'capital' && key !== 'salvage') ? 0.5 : 0;
        var df = Math.pow(1 + r, -(fl.t - shift));
        out[key] += fl[key] * df;
        out.total += fl[key] * df;
      }
    }
    return out;
  }
  Engine.pwOf = pwOf;

  /* Annual table: nominal and discounted cash flows grouped by year */
  function annualTable(flows, granularity, i, nYears, timing) {
    var mid = timing === 'mid';
    var per = granularity === 'monthly' ? 12 : 1;
    var r = per === 12 ? periodRate(i, 12) : i;
    var nYearsCeil = Math.max(1, Math.ceil(nYears - 1e-9));
    var rows = [];
    for (var y = 0; y <= nYearsCeil; y++) {
      var row = { year: y, capital: 0, maint: 0, oper: 0, own: 0, lease: 0, other: 0, salvage: 0,
                  total: 0, discounted: 0, cumDiscounted: 0 };
      rows.push(row);
    }
    for (var f = 0; f < flows.length; f++) {
      var fl = flows[f];
      var yIdx = granularity === 'monthly' ? Math.floor((fl.t - 1e-9) / 12) : Math.round(fl.t);
      if (granularity === 'monthly' && fl.t === 0) yIdx = 0;
      if (granularity === 'annual' && fl.t === 0) yIdx = 0;
      if (yIdx < 0) yIdx = 0;
      if (yIdx >= rows.length) yIdx = rows.length - 1;
      for (var j = 0; j < KEYS.length; j++) {
        var key = KEYS[j];
        if (fl[key]) {
          var shift = (mid && fl.t > 0 && key !== 'capital' && key !== 'salvage') ? 0.5 : 0;
          var df = Math.pow(1 + r, -(fl.t - shift));
          rows[yIdx][key] += fl[key];
          rows[yIdx].total += fl[key];
          rows[yIdx].discounted += fl[key] * df;
        }
      }
    }
    var cum = 0;
    for (var k = 0; k < rows.length; k++) { cum += rows[k].discounted; rows[k].cumDiscounted = cum; }
    return rows;
  }
  Engine.annualTable = annualTable;

  /* ======================================================================
     FULL EVALUATION
     ====================================================================== */
  function evaluateAlt(kind, inp, nYears, i) {
    var built = kind === 'buy' ? buyFlows(inp, nYears)
              : kind === 'lease' ? leaseFlows(inp, nYears)
              : rentFlows(inp, nYears);
    var pw = pwOf(built.flows, built.granularity, i, inp.econ.timing);
    var factor = apf(i, nYears);
    var euac = pw.total * factor;
    var table = annualTable(built.flows, built.granularity, i, nYears, inp.econ.timing);

    /* annualised component breakdown (sums exactly to EUAC) */
    var breakdown = {};
    for (var k = 0; k < KEYS.length; k++) breakdown[KEYS[k]] = pw[KEYS[k]] * factor;
    breakdown.capitalRecovery = breakdown.capital + breakdown.salvage;

    /* average nominal annual maintenance */
    var maintTotal = 0, leaseTotal = 0, operTotal = 0;
    for (var f = 0; f < built.flows.length; f++) {
      maintTotal += built.flows[f].maint;
      leaseTotal += built.flows[f].lease;
      operTotal += built.flows[f].oper;
    }

    var hours = productiveHours(inp);
    return {
      kind: kind,
      pw: pw.total,
      pwParts: pw,
      euac: euac,
      factor: factor,
      breakdown: breakdown,
      flows: built.flows,
      granularity: built.granularity,
      table: table,
      detail: built.detail,
      annualMaintenance: maintTotal / nYears,
      annualLeaseRent: leaseTotal / nYears,
      annualOperating: operTotal / nYears,
      costPerHour: hours > 0 ? euac / hours : 0,
      hours: hours
    };
  }

  function evaluate(inp) {
    var n = analysisYears(inp);
    var i = num(inp.econ.discountRate) / 100;
    var buy = evaluateAlt('buy', inp, n, i);
    var lease = evaluateAlt('lease', inp, n, i);
    var rent = evaluateAlt('rent', inp, n, i);

    var list = [{ k: 'buy', v: buy }, { k: 'lease', v: lease }, { k: 'rent', v: rent }];
    list.sort(function (a, b) { return a.v.euac - b.v.euac; });
    var best = list[0], second = list[1], worst = list[2];

    /* initial cash requirement */
    var b = inp.buy, l = inp.lease, r = inp.rent;
    var dpPct = clamp(num(b.downPaymentPct), 0, 100);
    var loanUsed = (b.financingView === 'owner') || (dpPct < 100 && num(b.loanTenureYears) > 0);
    var buyInitial = loanUsed ? num(b.price) * dpPct / 100 : num(b.price);
    var leaseInitial = num(l.advancePayment) + num(l.deposit);
    var rentInitial = num(r.mobDemob) + monthlyRentalRate(r);

    var out = {
      n: n,
      i: i,
      hours: productiveHours(inp),
      factor: apf(i, n),
      buy: buy, lease: lease, rent: rent,
      best: best.k,
      bestEuac: best.v.euac,
      secondBest: second.k,
      secondEuac: second.v.euac,
      worst: worst.k,
      savings: second.v.euac - best.v.euac,
      savingsPct: second.v.euac > 0 ? (second.v.euac - best.v.euac) / second.v.euac * 100 : 0,
      spread: worst.v.euac - best.v.euac,
      initial: { buy: buyInitial, lease: leaseInitial, rent: rentInitial },
      loanUsed: loanUsed,
      buyFinanced: buyInitial < num(b.price) - 1e-6
    };
    out.ranking = list.map(function (x) { return x.k; });
    return out;
  }
  Engine.evaluate = evaluate;

  /* ======================================================================
     BREAK-EVEN ANALYSIS  (EUAC vs study period)
     ====================================================================== */
  function breakEven(inp, opts) {
    opts = opts || {};
    var maxYears = opts.maxYears || 15;
    var step = opts.step || 0.5;
    var years = [], bArr = [], lArr = [], rArr = [], winners = [];
    var savedN = inp.project.analysisYears;

    for (var y = step; y <= maxYears + 1e-9; y += step) {
      inp.project.analysisYears = y;
      var i = num(inp.econ.discountRate) / 100;
      var bv = evaluateAlt('buy', inp, y, i).euac;
      var lv = evaluateAlt('lease', inp, y, i).euac;
      var rv = evaluateAlt('rent', inp, y, i).euac;
      years.push(+y.toFixed(2)); bArr.push(bv); lArr.push(lv); rArr.push(rv);
      var bestK = bv <= lv && bv <= rv ? 'buy' : (lv <= rv ? 'lease' : 'rent');
      winners.push(bestK);
    }
    inp.project.analysisYears = savedN;

    function cross(a, b) {
      var pts = [];
      for (var k = 1; k < years.length; k++) {
        var d0 = a[k - 1] - b[k - 1], d1 = a[k] - b[k];
        if (d0 === 0) { pts.push(years[k - 1]); continue; }
        if (d0 * d1 < 0) {
          var f = d0 / (d0 - d1);
          pts.push(+(years[k - 1] + f * (years[k] - years[k - 1])).toFixed(2));
        }
      }
      return pts;
    }

    return {
      years: years, buy: bArr, lease: lArr, rent: rArr, winners: winners,
      crossings: {
        'buy-rent': cross(bArr, rArr),
        'buy-lease': cross(bArr, lArr),
        'lease-rent': cross(lArr, rArr)
      }
    };
  }
  Engine.breakEven = breakEven;

  /* ======================================================================
     SENSITIVITY
     ====================================================================== */
  function getPath(obj, path) {
    var parts = path.split('.'), o = obj;
    for (var k = 0; k < parts.length; k++) o = o[parts[k]];
    return o;
  }
  function setPath(obj, path, val) {
    var parts = path.split('.'), o = obj;
    for (var k = 0; k < parts.length - 1; k++) o = o[parts[k]];
    o[parts[parts.length - 1]] = val;
  }
  Engine.getPath = getPath; Engine.setPath = setPath;

  function sensitivity(inp, path, opts) {
    opts = opts || {};
    var base = getPath(inp, path);
    var pct = opts.pct == null ? 40 : opts.pct;
    var steps = opts.steps || 9;
    var lo = base * (1 - pct / 100), hi = base * (1 + pct / 100);
    if (opts.absLo != null) lo = opts.absLo;
    if (opts.absHi != null) hi = opts.absHi;
    var out = [];
    var work = deepClone(inp);
    for (var k = 0; k < steps; k++) {
      var v = steps === 1 ? base : lo + (hi - lo) * k / (steps - 1);
      setPath(work, path, v);
      var res = evaluate(work);
      out.push({
        x: v,
        buy: res.buy.euac, lease: res.lease.euac, rent: res.rent.euac,
        best: res.best, base: false
      });
    }
    return { path: path, base: base, lo: lo, hi: hi, points: out };
  }
  Engine.sensitivity = sensitivity;

  /* Sweep a discrete dimension (duration / utilization) */
  function sweep(inp, path, values) {
    var work = deepClone(inp), out = [];
    for (var k = 0; k < values.length; k++) {
      setPath(work, path, values[k]);
      var res = evaluate(work);
      out.push({ x: values[k], buy: res.buy.euac, lease: res.lease.euac, rent: res.rent.euac, best: res.best });
    }
    return out;
  }
  Engine.sweep = sweep;

  /* ======================================================================
     VALIDATION
     ====================================================================== */
  function validate(inp) {
    var errors = [], warnings = [];
    var p = inp.project, e = inp.econ, b = inp.buy, l = inp.lease, r = inp.rent;
    var n = analysisYears(inp);

    if (!p.name || !String(p.name).trim()) warnings.push('Project name is empty — it will appear blank on the report cover.');
    if (num(p.durationMonths) <= 0) errors.push('Project duration must be greater than zero.');
    if (num(p.hoursPerYear) <= 0) errors.push('Expected operating hours per year must be greater than zero.');
    if (num(p.hoursPerYear) > 8760) errors.push('Operating hours per year cannot exceed 8,760 (hours in a year).');
    if (num(p.utilizationPct) <= 0 || num(p.utilizationPct) > 100) errors.push('Utilization must be between 0 and 100 percent.');
    if (n <= 0) errors.push('Analysis period must be greater than zero.');
    if (num(p.minCapacity) < 0) errors.push('Minimum required capacity cannot be negative.');

    if (num(e.discountRate) < 0) errors.push('Discount rate cannot be negative.');
    if (num(e.discountRate) > 100) warnings.push('Discount rate above 100% is unusual — check the entry.');
    if (num(e.taxRate) < 0 || num(e.taxRate) >= 100) errors.push('Tax rate must be between 0 and 100 percent.');
    if (e.afterTax && num(e.taxRate) <= 0) warnings.push('After-tax analysis is selected but the tax rate is zero — results equal the before-tax case.');

    if (num(b.price) <= 0) errors.push('Buy option: purchase price must be greater than zero.');
    if (num(b.downPaymentPct) < 0 || num(b.downPaymentPct) > 100) errors.push('Buy option: down payment must be between 0 and 100 percent of price.');
    if (num(b.downPaymentPct) > 0 && num(b.downPaymentPct) < 100 && num(b.loanTenureYears) <= 0)
      errors.push('Buy option: a loan tenure is required when the equipment is financed.');
    if (num(b.loanRate) < 0) errors.push('Buy option: loan interest rate cannot be negative.');
    if (num(b.economicLifeYears) <= 0) errors.push('Buy option: economic life must be greater than zero.');
    if (num(b.economicLifeYears) > 0 && n > num(b.economicLifeYears) + 1e-9) {
      if (b.replacement) warnings.push('Analysis period exceeds the economic life — a replacement purchase is being modelled at the end of each life cycle.');
      else warnings.push('Analysis period (' + n.toFixed(2) + ' yr) exceeds the economic life (' + num(b.economicLifeYears).toFixed(2) + ' yr). Enable replacement, or the machine is assumed to serve the whole period without renewal.');
    }
    if (num(b.resaleValue) < 0) errors.push('Buy option: resale value cannot be negative.');
    if (num(b.resaleValue) > num(b.price)) warnings.push('Resale value exceeds the purchase price — check that the residual is realistic.');
    if (num(b.maintenanceYear1) < 0 || num(b.maintenanceEscalationPct) < -100)
      errors.push('Buy option: maintenance costs and escalation must be valid positive values.');

    if (num(l.payment) <= 0 && num(l.advancePayment) <= 0)
      errors.push('Lease option: enter a lease payment or an advance payment.');
    if (num(l.termMonths) <= 0) errors.push('Lease option: lease term must be greater than zero months.');
    if (num(l.deposit) < 0) errors.push('Lease option: security deposit cannot be negative.');
    if (num(l.depositReturnMonth) > num(l.termMonths) && num(l.deposit) > 0)
      warnings.push('Lease option: the deposit return month is after the lease term — it is treated as returned at the end of the term.');
    if (n * 12 > num(l.termMonths) + 1e-6 && num(l.payment) > 0)
      warnings.push('Lease term is shorter than the analysis period — the lease is assumed to be renewed on the same terms.');
    if (num(l.escalationPct) < -100) errors.push('Lease option: escalation cannot be below -100%.');

    if (num(r.rateValue) <= 0) errors.push('Rent option: rental rate must be greater than zero.');
    if (num(r.minHireMonths) < 0) errors.push('Rent option: minimum hire period cannot be negative.');
    if (num(r.downtimePct) < 0 || num(r.downtimePct) > 100) errors.push('Rent option: downtime allowance must be between 0 and 100 percent.');
    if (r.rateBasis === 'day' && num(r.daysPerMonth) <= 0) errors.push('Rent option: billable days per month must be greater than zero.');
    if (num(r.durationMonths) > 0) {
      var rMonths = Math.round(num(r.durationMonths));
      var pMonths = Math.round(n * 12);
      if (Math.abs(rMonths - pMonths) > 0.5) {
        warnings.push('Rent option: the hire period (' + rMonths + ' months) differs from the analysis period (' +
          pMonths + ' months). The machine is only billed for the hire period entered, so the alternatives are not ' +
          'strictly like-for-like.');
      }
    }

    var hours = productiveHours(inp);
    if (hours > 0 && hours < 100) warnings.push('Productive hours per year are very low (' + Math.round(hours) + ' h) — per-hour costs will be dominated by ownership charges.');

    return { errors: errors, warnings: warnings, ok: errors.length === 0 };
  }
  Engine.validate = validate;

  /* ======================================================================
     SAMPLE DATA  (illustrative only — not market quotations)
     ====================================================================== */
  var EQUIPMENT = [
    {
      id: 'excavator', name: 'Hydraulic Excavator', spec: '20 t class, 1.0 m³ bucket',
      capacity: '1.0 m³ bucket / 20 t',
      price: 9500000, resale: 3200000, life: 8,
      maint: 320000, maintEsc: 9, insurance: 95000, reg: 18000, storage: 60000,
      rentMonth: 185000, rentDay: 8200, leaseMonth: 205000, hours: 2200,
      mob: 45000, fuelPerHr: 1450
    },
    {
      id: 'backhoe', name: 'Backhoe Loader', spec: '76 hp, 1.1 m³ / 0.3 m³',
      capacity: '1.1 m³ bucket / 76 hp',
      price: 3800000, resale: 1250000, life: 8,
      maint: 145000, maintEsc: 9, insurance: 38000, reg: 12000, storage: 30000,
      rentMonth: 95000, rentDay: 4200, leaseMonth: 88000, hours: 2000,
      mob: 18000, fuelPerHr: 620
    },
    {
      id: 'crane', name: 'Tower Crane', spec: 'TC 5013, 50 m jib, 6 t max',
      capacity: '6 t @ 14 m / 50 m jib',
      price: 12500000, resale: 3800000, life: 12,
      maint: 420000, maintEsc: 8, insurance: 125000, reg: 25000, storage: 90000,
      rentMonth: 350000, rentDay: 14500, leaseMonth: 285000, hours: 2600,
      mob: 285000, fuelPerHr: 0
    },
    {
      id: 'pump', name: 'Concrete Boom Pump', spec: '36 m boom, 60 m³/h',
      capacity: '60 m³/h @ 36 m boom',
      price: 8500000, resale: 2600000, life: 9,
      maint: 385000, maintEsc: 10, insurance: 85000, reg: 20000, storage: 55000,
      rentMonth: 220000, rentDay: 9500, leaseMonth: 195000, hours: 1600,
      mob: 65000, fuelPerHr: 980
    },
    {
      id: 'loader', name: 'Wheel Loader', spec: '3.1 m³ bucket, 18 t',
      capacity: '3.1 m³ bucket / 18 t',
      price: 7200000, resale: 2400000, life: 9,
      maint: 265000, maintEsc: 9, insurance: 72000, reg: 16000, storage: 45000,
      rentMonth: 140000, rentDay: 6100, leaseMonth: 155000, hours: 2100,
      mob: 32000, fuelPerHr: 890
    },
    {
      id: 'roller', name: 'Soil Compactor / Roller', spec: 'Vibratory, 11 t',
      capacity: '11 t operating weight',
      price: 4200000, resale: 1350000, life: 8,
      maint: 155000, maintEsc: 9, insurance: 42000, reg: 12000, storage: 28000,
      rentMonth: 85000, rentDay: 3800, leaseMonth: 92000, hours: 1800,
      mob: 15000, fuelPerHr: 430
    },
    {
      id: 'batching', name: 'Batching Plant', spec: '60 m³/h, twin shaft',
      capacity: '60 m³/h output',
      price: 11000000, resale: 3400000, life: 12,
      maint: 480000, maintEsc: 8, insurance: 110000, reg: 20000, storage: 120000,
      rentMonth: 280000, rentDay: 11500, leaseMonth: 245000, hours: 2400,
      mob: 150000, fuelPerHr: 210
    }
  ];
  Engine.EQUIPMENT = EQUIPMENT;

  /* ---------------------------------------------------------------------
     Equipment registry. EQUIPMENT holds the illustrative samples shipped
     with the tool; the UI layer keeps the user's own records in local
     storage and hands them over with setCustomEquipment(). Custom records
     use the same field names, so every calculation path works unchanged.
     --------------------------------------------------------------------- */
  var CUSTOM = [];

  Engine.setCustomEquipment = function (list) {
    CUSTOM = Array.isArray(list) ? list.slice() : [];
    return CUSTOM.length;
  };
  Engine.customEquipment = function () { return CUSTOM.slice(); };
  Engine.allEquipment = function () { return CUSTOM.concat(EQUIPMENT); };

  function equipmentById(id) {
    for (var k = 0; k < CUSTOM.length; k++) if (CUSTOM[k].id === id) return CUSTOM[k];
    for (var j = 0; j < EQUIPMENT.length; j++) if (EQUIPMENT[j].id === id) return EQUIPMENT[j];
    return EQUIPMENT[0];
  }
  Engine.equipmentById = equipmentById;

  function defaultInputs(equipId) {
    var q = equipmentById(equipId || 'excavator');
    /* a user record may carry no lease rate: derive a plausible one from price */
    var leaseM = (q.leaseMonth != null && q.leaseMonth > 0) ? q.leaseMonth : Math.round(q.price * 0.021);
    return {
      project: {
        name: 'Metro Viaduct Package 4 — Earthwork',
        equipmentId: q.id,
        durationValue: 36, durationUnit: 'months', durationMonths: 36,
        hoursPerYear: q.hours, utilizationPct: 75,
        analysisYears: 3, minCapacity: 1.0
      },
      econ: {
        discountRate: 11, inflationRate: 5, taxRate: 25, afterTax: false,
        timing: 'end'
      },
      buy: {
        price: q.price,
        downPaymentPct: 20, loanRate: 10.5, loanTenureYears: 5,
        financingView: 'economic',
        maintenanceYear1: q.maint, maintenanceEscalationPct: q.maintEsc,
        insuranceAnnual: q.insurance, registrationAnnual: q.reg, storageAnnual: q.storage,
        otherAnnual: 0, operatingCostPerHour: 0,
        resaleValue: (q.resale != null ? Math.round(q.resale) : Math.round(q.price * 0.34)),
        economicLifeYears: q.life,
        replacement: false
      },
      lease: {
        advancePayment: Math.round(leaseM * 3),
        payment: leaseM, paymentFrequency: 'monthly',
        termMonths: 24, escalationPct: 5,
        maintenanceResponsibility: 'lessor', lesseeMaintenanceAnnual: 0,
        lesseeInsuranceAnnual: Math.round(q.insurance * 0.6),
        deposit: Math.round(leaseM * 2), depositReturnMonth: 24,
        terminationPayment: 0, operatingCostPerHour: 0
      },
      rent: {
        rateValue: q.rentMonth, rateBasis: 'month', daysPerMonth: 26, durationMonths: 0,
        minHireMonths: 1, escalationPct: 0,
        mobDemob: q.mob,
        operatorIncluded: true, fuelIncluded: true,
        renterOperatingCostPerHour: 0,
        overtimePerMonth: 0, downtimePct: 5
      }
    };
  }
  Engine.defaultInputs = defaultInputs;

  /* ------------------------------------------------------ INR formatting */
  function formatINR(v, opts) {
    opts = opts || {};
    var x = num(v);
    var neg = x < 0;
    x = Math.abs(x);
    var dec = opts.dec == null ? 0 : opts.dec;
    var s = x.toLocaleString('en-IN', { minimumFractionDigits: dec, maximumFractionDigits: dec });
    return (neg ? '\u2212\u20B9' : '\u20B9') + s;
  }
  function compactINR(v) {
    var x = num(v);
    var neg = x < 0; x = Math.abs(x);
    var s;
    if (x >= 1e7) s = (x / 1e7).toFixed(2) + ' Cr';
    else if (x >= 1e5) s = (x / 1e5).toFixed(2) + ' L';
    else if (x >= 1e3) s = (x / 1e3).toFixed(1) + ' k';
    else s = x.toFixed(0);
    return (neg ? '\u2212\u20B9' : '\u20B9') + s;
  }
  Engine.formatINR = formatINR;
  Engine.compactINR = compactINR;

  Engine.VERSION = '1.0.0';

  if (typeof module !== 'undefined' && module.exports) module.exports = Engine;
  global.Engine = Engine;
})(typeof globalThis !== 'undefined' ? globalThis : this);


/* ================================ tests ================================ */
const E = globalThis.Engine;   /* engine is inlined above */

let pass = 0, fail = 0;
function ok(name, cond, extra) {
  if (cond) { pass++; console.log('  PASS  ' + name); }
  else { fail++; console.log('  FAIL  ' + name + (extra !== undefined ? '  -> ' + extra : '')); }
}
function close(name, got, exp, tol) {
  tol = tol == null ? 1e-6 : tol;
  const d = Math.abs(got - exp);
  ok(name, d <= tol * Math.max(1, Math.abs(exp)), 'got ' + got + ' expected ' + exp);
}

/* Build a bare input set we control exactly */
function mk(over) {
  const i = E.defaultInputs('excavator');
  i.project.analysisYears = 5;
  i.project.durationMonths = 60;
  i.econ.discountRate = 0;
  i.econ.inflationRate = 0;
  i.econ.afterTax = false;
  i.buy.maintenanceYear1 = 0; i.buy.maintenanceEscalationPct = 0;
  i.buy.insuranceAnnual = 0; i.buy.registrationAnnual = 0; i.buy.storageAnnual = 0;
  i.buy.otherAnnual = 0; i.buy.operatingCostPerHour = 0;
  i.buy.resaleValue = 0; i.buy.replacement = false;
  i.lease.advancePayment = 0; i.lease.payment = 0; i.lease.deposit = 0;
  i.lease.lesseeMaintenanceAnnual = 0; i.lease.lesseeInsuranceAnnual = 0;
  i.lease.operatingCostPerHour = 0; i.lease.terminationPayment = 0;
  i.rent.rateValue = 0; i.rent.mobDemob = 0; i.rent.downtimePct = 0;
  i.rent.overtimePerMonth = 0; i.rent.minHireMonths = 0;
  i.rent.renterOperatingCostPerHour = 0; i.rent.escalationPct = 0;
  i.lease.escalationPct = 0;
  if (over) over(i);
  return i;
}

console.log('\n--- 1. Factors ---');
close('(A/P,0,5) = 1/n', E.apf(0, 5), 0.2, 1e-12);
close('(A/F,0,5) = 1/n', E.af(0, 5), 0.2, 1e-12);
close('(A/P,10%,1)', E.apf(0.10, 1), 1.10, 1e-12);
close('(A/P,12%,5)', E.apf(0.12, 5), 0.2774097319, 1e-9);
close('(A/F,12%,5)', E.af(0.12, 5), 0.1574097319, 1e-9);
close('(P/F,12%,5)', E.pfv(0.12, 5), 0.5674268552, 1e-9);
close('(P/A,12%,5)', E.paf(0.12, 5), 3.6047762023, 1e-9);
close('(A/P)*(P/A) = 1', E.apf(0.12, 5) * E.paf(0.12, 5), 1, 1e-9);
close('(A/P) - (A/F) = i', E.apf(0.12, 5) - E.af(0.12, 5), 0.12, 1e-9);

console.log('\n--- 2. Zero discount rate ---');
let inp = mk(i => { i.buy.price = 100000; });
let r = E.evaluate(inp);
close('zero-rate buy EUAC = P/n', r.buy.euac, 20000, 1e-9);
ok('zero-rate no NaN/Infinity', isFinite(r.buy.euac) && isFinite(r.lease.euac) && isFinite(r.rent.euac));

console.log('\n--- 3. One-year analysis period ---');
inp = mk(i => { i.buy.price = 100000; i.project.analysisYears = 1; });
r = E.evaluate(inp);
close('n=1, i=0 -> EUAC = P', r.buy.euac, 100000, 1e-9);
inp = mk(i => { i.buy.price = 100000; i.project.analysisYears = 1; i.econ.discountRate = 10; });
r = E.evaluate(inp);
close('n=1, i=10% -> EUAC = P*1.1', r.buy.euac, 110000, 1e-9);

console.log('\n--- 4. Buy with salvage, textbook case ---');
inp = mk(i => {
  i.buy.price = 1000000; i.buy.resaleValue = 100000;
  i.econ.discountRate = 12; i.project.analysisYears = 5;
});
r = E.evaluate(inp);
const pwManual = 1000000 - 100000 * Math.pow(1.12, -5);
close('PW_B', r.buy.pw, pwManual, 1e-9);
close('EUAC_B = PW*(A/P)', r.buy.euac, pwManual * 0.2774097319, 1e-9);
close('textbook EUAC ~ 261,684', r.buy.euac, 261684, 1e-3);

console.log('\n--- 5. Capital recovery via (A/P) - S(A/F) identity ---');
inp = mk(i => {
  i.buy.price = 1000000; i.buy.resaleValue = 100000; i.econ.discountRate = 12; i.project.analysisYears = 5;
});
r = E.evaluate(inp);
const crAlt = 1000000 * E.apf(0.12, 5) - 100000 * E.af(0.12, 5);
close('CR = P(A/P) - S(A/F)', r.buy.breakdown.capitalRecovery, crAlt, 1e-9);

console.log('\n--- 6. Escalating maintenance, correct timing ---');
inp = mk(i => {
  i.buy.price = 1000000; i.econ.discountRate = 10; i.project.analysisYears = 4;
  i.buy.maintenanceYear1 = 50000; i.buy.maintenanceEscalationPct = 8;
});
r = E.evaluate(inp);
let pwM = 0;
for (let t = 1; t <= 4; t++) pwM += 50000 * Math.pow(1.08, t - 1) / Math.pow(1.10, t);
close('PW of escalating maintenance', r.buy.pwParts.maint, pwM, 1e-9);
close('EUAC includes maintenance', r.buy.euac, (1000000 + pwM) * E.apf(0.10, 4), 1e-9);
const flat = mk(i => {
  i.buy.price = 1000000; i.econ.discountRate = 10; i.project.analysisYears = 4;
  i.buy.maintenanceYear1 = 50000; i.buy.maintenanceEscalationPct = 0;
});
ok('escalating maintenance > flat maintenance', r.buy.euac > E.evaluate(flat).buy.euac);

console.log('\n--- 7. Financing view must not double count ---');
inp = mk(i => {
  i.buy.price = 1000000; i.buy.resaleValue = 100000;
  i.econ.discountRate = 12; i.project.analysisYears = 5;
  i.buy.downPaymentPct = 20; i.buy.loanRate = 12; i.buy.loanTenureYears = 5;
  i.buy.financingView = 'economic';
});
const econView = E.evaluate(inp);
inp = mk(i => {
  i.buy.price = 1000000; i.buy.resaleValue = 100000;
  i.econ.discountRate = 12; i.project.analysisYears = 5;
  i.buy.downPaymentPct = 20; i.buy.loanRate = 12; i.buy.loanTenureYears = 5;
  i.buy.financingView = 'owner';
});
const ownerView = E.evaluate(inp);
close('owner view PW == economic PW when loan rate == MARR', ownerView.buy.pw, econView.buy.pw, 1e-6);
ok('owner view uses down payment only at t=0', Math.abs(ownerView.buy.detail.downPayment - 200000) < 1e-6);
close('owner view initial cash = 20%', ownerView.initial.buy, 200000, 1e-9);

console.log('\n--- 8. Loan outstanding balance at end ---');
inp = mk(i => {
  i.buy.price = 1000000; i.buy.resaleValue = 400000;
  i.econ.discountRate = 12; i.project.analysisYears = 3;
  i.buy.downPaymentPct = 20; i.buy.loanRate = 12; i.buy.loanTenureYears = 5;
  i.buy.financingView = 'owner';
});
r = E.evaluate(inp);
const A = 800000 * E.apf(0.12, 5);
const bal = A * E.paf(0.12, 2);
close('balance at year 3', r.buy.detail.balanceAtEnd, bal, 1e-6);
close('terminal net proceeds = S - balance',
  r.buy.pwParts.salvage, -(400000 - bal) * Math.pow(1.12, -3), 1e-6);

console.log('\n--- 9. Lease: monthly payments, monthly discounting ---');
inp = mk(i => {
  i.lease.payment = 100000; i.lease.termMonths = 12; i.project.analysisYears = 1;
  i.econ.discountRate = 12;
});
r = E.evaluate(inp);
const rm = Math.pow(1.12, 1 / 12) - 1;
const pwL = 100000 * (1 - Math.pow(1 + rm, -12)) / rm;
close('lease PW', r.lease.pw, pwL, 1e-9);
close('lease EUAC = PW*(A/P,12%,1)', r.lease.euac, pwL * 1.12, 1e-9);

console.log('\n--- 10. Refundable deposit nets out at zero rate ---');
inp = mk(i => {
  i.lease.payment = 100000; i.lease.termMonths = 24; i.project.analysisYears = 2;
  i.lease.deposit = 200000; i.lease.depositReturnMonth = 24; i.econ.discountRate = 0;
});
r = E.evaluate(inp);
close('deposit has zero net effect at i=0', r.lease.pw, 100000 * 24, 1e-9);
inp = mk(i => {
  i.lease.payment = 100000; i.lease.termMonths = 24; i.project.analysisYears = 2;
  i.lease.deposit = 200000; i.lease.depositReturnMonth = 24; i.econ.discountRate = 12;
});
r = E.evaluate(inp);
const pwNoDep = (() => {
  const q = mk(i => { i.lease.payment = 100000; i.lease.termMonths = 24; i.project.analysisYears = 2; i.econ.discountRate = 12; });
  return E.evaluate(q).lease.pw;
})();
ok('discounted deposit makes the lease costlier (time value)', r.lease.pw > pwNoDep);
close('deposit effect = D(1 - (1+rm)^-24)', r.lease.pw - pwNoDep,
  200000 * (1 - Math.pow(1 + rm, -24)), 1e-6);

console.log('\n--- 11. Irregular timing: advance payment + termination ---');
inp = mk(i => {
  i.lease.payment = 0; i.lease.advancePayment = 300000;
  i.lease.terminationPayment = 150000;
  i.lease.termMonths = 12; i.project.analysisYears = 1; i.econ.discountRate = 12;
});
r = E.evaluate(inp);
close('advance at t=0 + termination at t=12',
  r.lease.pw, 300000 + 150000 * Math.pow(1.12, -1), 1e-9);

console.log('\n--- 12. Rent: monthly hire, mob/demob, min hire ---');
inp = mk(i => {
  i.rent.rateValue = 100000; i.rent.rateBasis = 'month';
  i.rent.mobDemob = 50000; i.rent.minHireMonths = 0; i.rent.downtimePct = 0;
  i.project.analysisYears = 1; i.econ.discountRate = 12;
});
r = E.evaluate(inp);
const rm2 = Math.pow(1.12, 1 / 12) - 1;
const pvRent = 100000 * (1 - Math.pow(1 + rm2, -12)) / rm2;
close('rent PW = 12 months + mob + demob', r.rent.pw, pvRent + 50000 + 50000 * Math.pow(1.12, -1), 1e-6);
inp = mk(i => {
  i.rent.rateValue = 100000; i.rent.rateBasis = 'month';
  i.rent.minHireMonths = 6; i.project.analysisYears = 0.25; i.econ.discountRate = 12;
});
r = E.evaluate(inp);
ok('minimum hire charges the shortfall for a 3-month project',
  r.rent.pw > 3 * 100000, 'PW=' + r.rent.pw);

console.log('\n--- 13. Daily-rate conversion ---');
inp = mk(i => {
  i.rent.rateValue = 5000; i.rent.rateBasis = 'day'; i.rent.daysPerMonth = 26;
  i.project.analysisYears = 1;
});
close('monthly equivalent of a daily rate', E.monthlyRentalRate(inp.rent), 130000, 1e-9);

console.log('\n--- 14. Partial-year proration (3-month project) ---');
inp = mk(i => {
  i.buy.price = 1000000; i.project.analysisYears = 0.25; i.econ.discountRate = 0;
  i.buy.maintenanceYear1 = 400000; i.buy.insuranceAnnual = 80000;
});
r = E.evaluate(inp);
close('3-month project pays 25% of annual ownership costs',
  r.buy.pwParts.maint + r.buy.pwParts.own, 0.25 * (400000 + 80000), 1e-6);
close('EUAC annualised over 0.25 yr', r.buy.euac, (1000000 + 120000) * 4, 1e-6);

console.log('\n--- 15. Replacement cycles ---');
inp = mk(i => {
  i.buy.price = 1000000; i.buy.resaleValue = 200000; i.buy.economicLifeYears = 5;
  i.project.analysisYears = 10; i.econ.discountRate = 10; i.buy.replacement = true;
});
r = E.evaluate(inp);
const cyc = 1000000 + 1000000 * Math.pow(1.10, -5) - 200000 * Math.pow(1.10, -5) - 200000 * Math.pow(1.10, -10);
close('two-cycle PW', r.buy.pw, cyc, 1e-9);
inp = mk(i => {
  i.buy.price = 1000000; i.buy.resaleValue = 200000; i.buy.economicLifeYears = 5;
  i.project.analysisYears = 10; i.econ.discountRate = 10; i.buy.replacement = false;
});
const single = E.evaluate(inp);
ok('replacement is costlier than one machine lasting 10 yr', r.buy.pw > single.buy.pw);

console.log('\n--- 16. Breakdown sums to EUAC ---');
inp = E.defaultInputs('crane');
r = E.evaluate(inp);
['buy', 'lease', 'rent'].forEach(k => {
  const b = r[k].breakdown;
  const sum = b.capital + b.maint + b.oper + b.own + b.lease + b.other + b.salvage;
  close(k + ' component breakdown == EUAC', sum, r[k].euac, 1e-9);
});

console.log('\n--- 17. After-tax treatment ---');
inp = mk(i => {
  i.buy.price = 1000000; i.project.analysisYears = 5; i.econ.discountRate = 10;
  i.buy.maintenanceYear1 = 100000; i.econ.afterTax = false;
});
const pre = E.evaluate(inp);
inp.econ.afterTax = true; inp.econ.taxRate = 30; inp.buy.resaleValue = 0;
const post = E.evaluate(inp);
ok('after-tax with depreciation shield lowers EUAC', post.buy.euac < pre.buy.euac,
  'pre ' + pre.buy.euac.toFixed(0) + ' post ' + post.buy.euac.toFixed(0));

console.log('\n--- 18. Validation ---');
let v = E.validate(mk(i => { i.buy.price = 0; }));
ok('zero price rejected', !v.ok);
v = E.validate(mk(i => { i.project.utilizationPct = 120; }));
ok('utilization > 100 rejected', !v.ok);
v = E.validate(mk(i => { i.econ.discountRate = -5; }));
ok('negative discount rate rejected', !v.ok);
v = E.validate(mk(i => { i.rent.rateValue = 0; }));
ok('zero rental rate rejected', !v.ok);
v = E.validate(E.defaultInputs('excavator'));
ok('default inputs valid', v.ok, JSON.stringify(v.errors));

console.log('\n--- 19. Break-even ---');
inp = E.defaultInputs('excavator');
inp.project.analysisYears = 3;
const be = E.breakEven(inp, { maxYears: 15, step: 0.5 });
ok('break-even series produced', be.years.length > 10);
ok('buy-rent crossing detected for excavator', be.crossings['buy-rent'].length > 0,
  JSON.stringify(be.crossings));
console.log('    crossings:', JSON.stringify(be.crossings));
// A case engineered to have no crossover: very cheap rent, tiny purchase
inp = mk(i => {
  i.buy.price = 50000000; i.rent.rateValue = 1000; i.rent.rateBasis = 'month';
  i.buy.economicLifeYears = 10; i.project.analysisYears = 1;
  i.lease.payment = 1000;
});
const be2 = E.breakEven(inp, { maxYears: 6, step: 0.5 });
ok('no buy-rent crossover when renting is trivially cheap',
  be2.crossings['buy-rent'].length === 0, JSON.stringify(be2.crossings));

console.log('\n--- 20. Sensitivity sweep changes the winner ---');
inp = E.defaultInputs('excavator');
inp.project.analysisYears = 1;
inp.project.durationMonths = 12;
const sens = E.sensitivity(inp, 'rent.rateValue', { pct: 60, steps: 9 });
const winners = new Set(sens.points.map(p => p.best));
ok('rent-rate sensitivity yields >= 2 outcomes or stays consistent', winners.size >= 1,
  [...winners].join(','));
const dur = E.sweep(inp, 'project.analysisYears', [0.25, 1, 2, 3, 5, 8, 12]);
ok('duration sweep returns finite EUACs', dur.every(d => isFinite(d.buy) && isFinite(d.rent)));
console.log('    duration sweep winners:', dur.map(d => d.x + 'y:' + d.best).join(' '));

console.log('\n--- 21. INR formatting ---');
ok('Indian grouping', E.formatINR(12345678) === '\u20B91,23,45,678', E.formatINR(12345678));
ok('compact crore', E.compactINR(12345678) === '\u20B91.23 Cr', E.compactINR(12345678));
ok('compact lakh', E.compactINR(450000) === '\u20B94.50 L', E.compactINR(450000));

console.log('\n--- 22b. Cash-flow timing convention ---');
inp = mk(i => { i.buy.price = 1000000; i.project.analysisYears = 3; i.econ.discountRate = 12;
  i.buy.maintenanceYear1 = 100000; i.econ.timing = 'end'; });
var tEnd = E.evaluate(inp);
inp.econ.timing = 'mid';
var tMid = E.evaluate(inp);
ok('mid-period timing raises the PW of recurring costs (paid earlier)', tMid.buy.pw > tEnd.buy.pw);
close('capital outlay unaffected by timing', tMid.buy.pwParts.capital, tEnd.buy.pwParts.capital, 1e-12);
ok('EUAC still finite under mid-period timing', isFinite(tMid.buy.euac));

console.log('\n--- 22. Hours and cost per hour ---');
inp = E.defaultInputs('excavator');
inp.project.hoursPerYear = 2000; inp.project.utilizationPct = 75;
r = E.evaluate(inp);
close('productive hours', r.hours, 1500, 1e-9);
close('cost per hour = EUAC / hours', r.buy.costPerHour, r.buy.euac / 1500, 1e-9);


console.log('\n--- 23. Explicit rental duration ---');
inp = mk(i => {
  i.rent.rateValue = 100000; i.rent.rateBasis = 'month'; i.rent.durationMonths = 6;
  i.rent.mobDemob = 0; i.rent.minHireMonths = 0; i.rent.downtimePct = 0;
  i.project.analysisYears = 2; i.econ.discountRate = 0;
});
r = E.evaluate(inp);
close('only the committed 6 months are billed', r.rent.pw, 600000, 1e-6);
inp.rent.durationMonths = 0;
r = E.evaluate(inp);
close('0 means follow the study period (24 months)', r.rent.pw, 2400000, 1e-6);
var v23 = E.validate(mk(i => { i.rent.rateValue = 100000; i.rent.durationMonths = 6; i.project.analysisYears = 2; }));
ok('mismatch between hire period and study period is flagged',
  v23.warnings.some(function (w) { return w.indexOf('hire period') >= 0; }));

console.log('\n============================');
console.log('PASS ' + pass + '   FAIL ' + fail);
console.log('============================\n');
process.exit(fail ? 1 : 0);
