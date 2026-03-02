/** Click button twice, body text contains "0 :: 0 :: []" (two-item list) */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/main');
  await page.waitForSelector('xpath=/html/body/button');
  await page.click('xpath=/html/body/button');
  await page.click('xpath=/html/body/button');
  // Wait for two list separators to appear in the body text
  await page.waitForFunction(() => {
    const t = document.body.textContent;
    return t.includes(' :: ') && t.includes('[]');
  });
  const bodyText = await page.evaluate(() => document.body.textContent);
  // The list shows two counters (both 0) and list separators
  if (!bodyText.includes(' :: ') || !bodyText.includes('[]')) {
    throw new Error(`Expected body text to contain list " :: " and "[]", got: ${bodyText}`);
  }
};
