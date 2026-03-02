/** Click checkbox, body text changes from "True 1" to "False 3" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Ccheckbox/main');
  // Wait for dyn to render initial content ("True 1")
  await page.waitForFunction(() => document.body.textContent.includes('True'));
  let txt = await page.evaluate(() => document.body.textContent);
  if (!txt.includes('True') || !txt.includes('1')) {
    throw new Error(`Expected body text "True 1", got: ${txt}`);
  }
  await page.click('xpath=/html/body/input');
  // Wait for dyn to update to "False 3"
  await page.waitForFunction(() => document.body.textContent.includes('False'));
  txt = await page.evaluate(() => document.body.textContent);
  if (!txt.includes('False') || !txt.includes('3')) {
    throw new Error(`Expected body text "False 3", got: ${txt}`);
  }
};
