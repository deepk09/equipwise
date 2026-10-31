# EquipWise — Buy vs Lease vs Rent (EUAC analysis)

A single-page, self-contained web application for comparing the acquisition of
construction equipment by **buying, leasing or renting**, using Equivalent
Uniform Annual Cost analysis.

## What is in this folder

| File | Purpose |
|---|---|
| `index.html` | The whole application. HTML, CSS, the calculation engine and the React interface, in one file. |
| `equipwise-engine-tests.js` | Automated test suite for the calculation engine (63 assertions). Run with `node equipwise-engine-tests.js`. |

`index.html` has no build step and no server-side code. It needs an internet
connection on first load because React, Chart.js and jsPDF come from public
CDNs; everything else is inline.

## Publishing it

Any static host works, because there is nothing to compile. Pick one:

**Netlify Drop** — go to app.netlify.com/drop and drag this whole folder onto
the page. You get a public URL in about ten seconds. No account needed to try.

**GitHub Pages** — create a repository, upload `index.html`, then Settings >
Pages > Source: deploy from branch, folder `/ (root)`. The site appears at
`https://<user>.github.io/<repo>/`.

**Vercel** — `vercel` in this folder, or drag the folder into the Vercel
dashboard. Framework preset: Other. No build command, output directory `.`.

**Cloudflare Pages** — create a project, upload the folder directly (Direct
Upload), no build step.

Because the file is fully static, you can also just email `index.html` and open
it locally — that path works identically, including the PDF report.

## Using the application

1. **Dashboard** — pick one of seven equipment categories, or add your own
   machine (name, price, resale, life, maintenance, insurance, rental and lease
   rates). Your records are stored in the browser's local storage.
   The same page holds the scenario manager: save the current assumptions under
   a name, then load, rename, duplicate or delete runs. **Export JSON** writes
   every scenario to a file and **Import JSON** reads one back, so scenarios can
   move between devices or be handed in alongside the report.
2. **Inputs** — project, economic parameters, and the buy / lease / rent
   assumptions. Validation messages appear as you type.
3. **Results** — EUAC for each alternative, comparison table, six charts, the
   formulas with your numbers substituted, and the annual cash-flow tables.
4. **Break-even** — the study period at which the preferred alternative changes,
   including the case where the curves never cross.
5. **Sensitivity** — eight variables flexed one at a time, plus 3-, 12- and
   36-month deployment scenarios.
6. **Report** — generates a multi-page PDF with inputs, formulas, cash-flow
   tables, charts and a written recommendation.

## A note on the numbers

The equipment prices, rentals and lease rates shipped with the tool are
illustrative study values, not market quotations. Every result is computed live
from whatever inputs are on screen, and the report states the assumptions it
used. Replace the sample figures with your own quotations before relying on any
result.

## Method

Present worth of each alternative's full cash-flow stream, annualised with the
capital recovery factor:

    PW_B = P + SUM[t=1..n] C_t/(1+i)^t - S/(1+i)^n
    EUAC = PW x (A/P, i, n),  (A/P, i, n) = i(1+i)^n / ((1+i)^n - 1)

Monthly lease and rental flows are discounted at the equivalent monthly rate
`(1+i)^(1/12) - 1`, not at `i/12`. The alternative with the lowest EUAC is
preferred, provided all three deliver the same equipment service.
