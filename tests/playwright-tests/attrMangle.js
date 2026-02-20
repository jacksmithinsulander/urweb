/** Click goofy element (name=beppo, data-role=excellence), expect alert */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/AttrMangle/main');
  const dlg = page.waitForEvent('dialog');
  await page.click('[name="beppo"][data-role="excellence"]');
  const alert = await dlg;
  if (alert.message() !== "You clicked it!  That's some fancy shooting!") {
    throw new Error(`Expected "You clicked it!...", got: ${alert.message()}`);
  }
  await alert.accept();
};
