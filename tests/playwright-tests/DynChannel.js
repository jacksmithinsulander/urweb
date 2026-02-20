/** Click Register, click Send, alert "Got something from the channel", span "blabla" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/DynChannel/main');
  await page.click('xpath=/html/body/button');
  await page.click('xpath=/html/body/span/button');
  const dlg = page.waitForEvent('dialog');
  const alert = await dlg;
  if (alert.message() !== 'Got something from the channel') {
    throw new Error(`Expected "Got something from the channel", got: ${alert.message()}`);
  }
  await alert.accept();
  const span = page.locator('xpath=/html/body/span/span');
  const txt = await span.textContent();
  if (txt !== 'blabla') {
    throw new Error(`Expected span "blabla", got: ${txt}`);
  }
};
