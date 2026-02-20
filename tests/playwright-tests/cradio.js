/** Radio selection, alerts, dynamic updates */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Cradio/main');
  const d1 = page.locator('xpath=/html/body/div[1]');
  const d2 = page.locator('xpath=/html/body/div[2]');
  let txt = await d1.textContent();
  if (txt !== "Hello, I'm B. I'll be your waiter for this evening.") {
    throw new Error(`Expected div1 "Hello, I'm B...", got: ${txt}`);
  }
  txt = await d2.textContent();
  if (txt !== 'Value:') {
    throw new Error(`Expected div2 "Value:", got: ${txt}`);
  }
  const r1 = page.locator('xpath=/html/body/label[1]/input');
  const r2 = page.locator('xpath=/html/body/label[2]/input');
  if (await r1.isChecked()) throw new Error('Radio 1 should not be selected');
  if (!(await r2.isChecked())) throw new Error('Radio 2 should be selected');
  const dlg = page.waitForEvent('dialog');
  await r1.click();
  const alert1 = await dlg;
  if (alert1.message() !== "Now it's A") {
    throw new Error(`Expected "Now it's A", got: ${alert1.message()}`);
  }
  await alert1.accept();
  if (!(await r1.isChecked())) throw new Error('Radio 1 should be selected after click');
  if (await r2.isChecked()) throw new Error('Radio 2 should not be selected');
  txt = await d1.textContent();
  if (txt !== "Hello, I'm A. I'll be your waiter for this evening.") {
    throw new Error(`Expected div1 "Hello, I'm A...", got: ${txt}`);
  }
  const r4 = page.locator('xpath=/html/body/label[4]/input');
  const dlg2 = page.waitForEvent('dialog');
  await r4.click();
  await (await dlg2).accept();
  txt = await d2.textContent();
  if (txt !== 'Value: Y') {
    throw new Error(`Expected div2 "Value: Y", got: ${txt}`);
  }
};
