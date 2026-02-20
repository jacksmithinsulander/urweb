/** Click button, alert "Some \btext" (backspace char) */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Jsbspace/main');
  const dlg = page.waitForEvent('dialog');
  await page.click('xpath=/html/body/button');
  const alert = await dlg;
  if (alert.message() !== 'Some \btext') {
    throw new Error(`Expected alert "Some \\btext", got: ${JSON.stringify(alert.message())}`);
  }
  await alert.accept();
};
