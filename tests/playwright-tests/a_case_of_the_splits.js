/** Click button twice, span matches (0) :: (1) :: [] */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/A_case_of_the_splits/main');
  const btn = page.locator('xpath=/html/body/button');
  await btn.click();
  await btn.click();
  const span = page.locator('xpath=/html/body/span');
  const txt = await span.textContent();
  const re = /.*\(0\).* :: .*\(1\).* :: \[\]/;
  if (!re.test(txt)) {
    throw new Error(`Expected span to match (0) :: (1) :: [], got: ${txt}`);
  }
};
