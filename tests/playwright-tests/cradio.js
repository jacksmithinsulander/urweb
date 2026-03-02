/** Radio selection, alerts, dynamic updates */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Cradio/main');
  // Wait for dyn in div[1] to render initial radio value "B"
  // Use innerText (excludes <script> content unlike textContent)
  await page.waitForFunction(() => {
    const div = document.querySelector('body > div');
    return div && div.innerText.includes("I'm B");
  });
  const d1 = page.locator('xpath=/html/body/div[1]');
  const d2 = page.locator('xpath=/html/body/div[2]');
  let txt = (await d1.innerText()).trim();
  if (txt !== "Hello, I'm B. I'll be your waiter for this evening.") {
    throw new Error(`Expected div1 "Hello, I'm B...", got: ${JSON.stringify(txt)}`);
  }
  txt = (await d2.innerText()).trim();
  if (txt !== 'Value:') {
    throw new Error(`Expected div2 "Value:", got: ${JSON.stringify(txt)}`);
  }
  const r1 = page.locator('xpath=/html/body/label[1]/input');
  const r2 = page.locator('xpath=/html/body/label[2]/input');
  if (await r1.isChecked()) throw new Error('Radio 1 should not be selected');
  if (!(await r2.isChecked())) throw new Error('Radio 2 should be selected');
  let dialogMsg1 = null;
  page.once('dialog', async dialog => {
    dialogMsg1 = dialog.message();
    await dialog.accept();
  });
  await r1.click();
  if (dialogMsg1 !== "Now it's A") {
    throw new Error(`Expected "Now it's A", got: ${dialogMsg1}`);
  }
  if (!(await r1.isChecked())) throw new Error('Radio 1 should be selected after click');
  if (await r2.isChecked()) throw new Error('Radio 2 should not be selected');
  // Wait for dyn to update to "A"
  await page.waitForFunction(() => {
    const div = document.querySelector('body > div');
    return div && div.innerText.includes("I'm A");
  });
  txt = (await d1.innerText()).trim();
  if (txt !== "Hello, I'm A. I'll be your waiter for this evening.") {
    throw new Error(`Expected div1 "Hello, I'm A...", got: ${JSON.stringify(txt)}`);
  }
  const r4 = page.locator('xpath=/html/body/label[4]/input');
  let dialogMsg2 = null;
  page.once('dialog', async dialog => {
    dialogMsg2 = dialog.message();
    await dialog.accept();
  });
  await r4.click();
  // Wait for dyn in div[2] to update to show "Y"
  await page.waitForFunction(() => {
    const divs = document.querySelectorAll('body > div');
    return divs.length >= 2 && divs[1].innerText.includes('Y');
  });
  txt = (await d2.innerText()).trim();
  if (txt !== 'Value: Y') {
    throw new Error(`Expected div2 "Value: Y", got: ${JSON.stringify(txt)}`);
  }
};
