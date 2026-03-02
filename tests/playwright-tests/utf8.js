/** Run all utf8 no_falses tests: each page must have <pre> elements all saying "True" */
module.exports = async (page, baseUrl) => {
  const noFalsesPages = [
    'Utf8/substrings', 'Utf8/strlens', 'Utf8/strlenGens', 'Utf8/strcats',
    'Utf8/strsubs', 'Utf8/strsuffixs', 'Utf8/strchrs', 'Utf8/strindexs',
    'Utf8/strsindexs', 'Utf8/strcspns', 'Utf8/str1s', 'Utf8/isalnums',
    'Utf8/isalphas', 'Utf8/isblanks', 'Utf8/iscntrls', 'Utf8/isdigits',
    'Utf8/isgraphs', 'Utf8/islowers', 'Utf8/isprints', 'Utf8/ispuncts',
    'Utf8/isspaces', 'Utf8/isuppers', 'Utf8/isxdigits', 'Utf8/touppers',
    'Utf8/ord_and_chrs', 'Utf8/test_db',
  ];

  for (const path of noFalsesPages) {
    await page.goto(baseUrl + '/' + path, { waitUntil: 'networkidle', timeout: 20000 });
    // Wait for at least one <pre> to appear (JS renders them)
    await page.waitForSelector('pre', { timeout: 15000 });
    const falses = await page.evaluate(() => {
      const pres = Array.from(document.querySelectorAll('pre'));
      return pres.filter(p => p.textContent.trim() === 'False').map(p => p.textContent);
    });
    if (falses.length > 0) {
      throw new Error(`${path}: found ${falses.length} False value(s)`);
    }
  }
};
