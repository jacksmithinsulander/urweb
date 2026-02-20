/** Cffi test 1: form 1 input click, button 2 click -> alert "<<Hoho>>", button 3 -> "Hi there!" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Cffi/main');
  await page.click('xpath=/html/body/form[1]/input');
  await page.click('xpath=/html/body/button[2]');
  const d1 = await page.waitForEvent('dialog');
  if (d1.message() !== '<<Hoho>>') {
    throw new Error(`Expected "<<Hoho>>", got: ${d1.message()}`);
  }
  await d1.accept();
  await page.click('xpath=/html/body/button[3]');
  const d2 = await page.waitForEvent('dialog');
  if (d2.message() !== 'Hi there!') {
    throw new Error(`Expected "Hi there!", got: ${d2.message()}`);
  }
  await d2.accept();
};
