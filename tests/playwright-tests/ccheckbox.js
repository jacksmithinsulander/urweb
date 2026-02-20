/** Click checkbox, span changes from "True 1" to "False 3" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Ccheckbox/main');
  const span = page.locator('xpath=/html/body/span');
  let txt = await span.textContent();
  if (!txt || !txt.includes('True') || !txt.includes('1')) {
    throw new Error(`Expected span "True 1", got: ${txt}`);
  }
  await page.click('xpath=/html/body/input');
  txt = await span.textContent();
  if (!txt || !txt.includes('False') || !txt.includes('3')) {
    throw new Error(`Expected span "False 3", got: ${txt}`);
  }
};
