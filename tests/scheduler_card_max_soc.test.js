import { describe, it, expect, vi, beforeAll, afterEach } from 'vitest';

beforeAll(async () => {
  await import('../custom_components/foxess/scheduler_card.js');
});

afterEach(() => {
  document.body.innerHTML = '';
});

const DEVICE_SN = 'SN123456';

function makeGroup(extraParam) {
  return {
    startHour: 6, startMinute: 0,
    endHour: 12, endMinute: 0,
    enable: 1,
    workMode: 'ForceCharge',
    extraParam,
  };
}

function makeHass(groups = [], sendOverride = null) {
  const send = sendOverride ?? vi.fn().mockImplementation(msg => {
    if (msg.type === 'foxess/get_templates') return Promise.resolve({ templates: [] });
    return Promise.resolve({ ok: true });
  });
  return {
    states: {
      'sensor.foxess_scheduler_enabled': {
        state: 'enabled',
        attributes: { friendly_name: 'FoxESS Scheduler Enabled' },
      },
      'sensor.foxess_scheduler_groups': {
        state: String(groups.length),
        attributes: { groups, device_sn: DEVICE_SN },
      },
    },
    connection: { sendMessagePromise: send },
  };
}

function mountCard(hass) {
  const Card = customElements.get('foxess-scheduler-card');
  const card = new Card();
  document.body.appendChild(card);
  card.hass = hass;
  return card;
}

async function tick() {
  await new Promise(resolve => setTimeout(resolve, 0));
}

// ---------------------------------------------------------------------------
// Main card table
// ---------------------------------------------------------------------------

describe('Max SoC - main card table', () => {
  it('has "Max SoC" column header after "FD Power"', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 80 })]));
    const headers = Array.from(card.shadowRoot.querySelectorAll('table thead th')).map(th => th.textContent.trim());
    const fdPowerIdx = headers.indexOf('FD Power');
    const maxSocIdx = headers.indexOf('Max SoC');
    expect(maxSocIdx).toBeGreaterThan(-1);
    expect(maxSocIdx).toBe(fdPowerIdx + 1);
  });

  it('renders maxSoc value from extraParam', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 75 })]));
    const cells = Array.from(card.shadowRoot.querySelectorAll('table tbody td'));
    expect(cells.some(td => td.textContent.trim() === '75%')).toBe(true);
  });

  it('defaults maxSoc to 100 when extraParam.maxSoc is absent', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000 })]));
    const cells = Array.from(card.shadowRoot.querySelectorAll('table tbody td'));
    expect(cells.some(td => td.textContent.trim() === '100%')).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// Edit modal
// ---------------------------------------------------------------------------

describe('Max SoC - edit modal', () => {
  it('has "Max SoC%" column header after "FD Pwr (W)"', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 80 })]));
    card.shadowRoot.querySelector('.edit-btn').click();
    const headers = Array.from(card.shadowRoot.querySelectorAll('.modal-table thead th')).map(th => th.textContent.trim());
    const fdPwrIdx = headers.indexOf('FD Pwr (W)');
    const maxSocIdx = headers.indexOf('Max SoC%');
    expect(maxSocIdx).toBeGreaterThan(-1);
    expect(maxSocIdx).toBe(fdPwrIdx + 1);
  });

  it('renders maxSoc input with the value from group data', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 75 })]));
    card.shadowRoot.querySelector('.edit-btn').click();
    const input = card.shadowRoot.querySelector('.num-input[data-field="maxSoc"]');
    expect(input).not.toBeNull();
    expect(input.value).toBe('75');
  });

  it('maxSoc input appears after fdPwr input in the DOM', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 80 })]));
    card.shadowRoot.querySelector('.edit-btn').click();
    const inputs = Array.from(card.shadowRoot.querySelectorAll('.num-input'));
    const fdPwrIdx = inputs.findIndex(i => i.dataset.field === 'fdPwr');
    const maxSocIdx = inputs.findIndex(i => i.dataset.field === 'maxSoc');
    expect(maxSocIdx).toBeGreaterThan(fdPwrIdx);
  });
});

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

describe('Max SoC - validation', () => {
  it('blocks save and shows error when maxSoc <= fdSoc', () => {
    const send = vi.fn().mockResolvedValue({ ok: true });
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 90, fdPwr: 0, maxSoc: 80 })], send));
    card.shadowRoot.querySelector('.edit-btn').click();
    card.shadowRoot.querySelector('.save-btn').click();
    expect(card.shadowRoot.querySelector('.modal-error').textContent).toBeTruthy();
    expect(send).not.toHaveBeenCalledWith(expect.objectContaining({ type: 'foxess/save_schedule' }));
  });

  it('blocks save and shows error when fdSoc <= minSocOnGrid', () => {
    const send = vi.fn().mockResolvedValue({ ok: true });
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 50, fdSoc: 30, fdPwr: 0, maxSoc: 100 })], send));
    card.shadowRoot.querySelector('.edit-btn').click();
    card.shadowRoot.querySelector('.save-btn').click();
    expect(card.shadowRoot.querySelector('.modal-error').textContent).toBeTruthy();
    expect(send).not.toHaveBeenCalledWith(expect.objectContaining({ type: 'foxess/save_schedule' }));
  });

  it('allows save to proceed when maxSoc > fdSoc > minSocOnGrid', async () => {
    const send = vi.fn().mockResolvedValue({ ok: true });
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 0, maxSoc: 90 })], send));
    card.shadowRoot.querySelector('.edit-btn').click();
    card.shadowRoot.querySelector('.save-btn').click();
    await tick();
    expect(send).toHaveBeenCalledWith(expect.objectContaining({ type: 'foxess/save_schedule' }));
    expect(card.shadowRoot.querySelector('.modal-error').textContent).toBe('');
  });
});

// ---------------------------------------------------------------------------
// Add remaining slot button
// ---------------------------------------------------------------------------

function makeHassForRemaining(groups = [], minSoc = 10, sendOverride = null) {
  const send = sendOverride ?? vi.fn().mockImplementation(msg => {
    if (msg.type === 'foxess/get_templates') return Promise.resolve({ templates: [] });
    return Promise.resolve({ ok: true });
  });
  return {
    states: {
      'sensor.foxess_scheduler_enabled': {
        state: 'enabled',
        attributes: { friendly_name: 'FoxESS Scheduler Enabled' },
      },
      'sensor.foxess_scheduler_groups': {
        state: String(groups.length),
        attributes: { groups, device_sn: DEVICE_SN, min_soc: minSoc },
      },
    },
    connection: { sendMessagePromise: send },
  };
}

const NORMAL_GROUP = {
  startHour: 6, startMinute: 0, endHour: 12, endMinute: 0,
  enable: 1, workMode: 'ForceCharge',
  extraParam: { minSocOnGrid: 10, fdSoc: 90, fdPwr: 0, maxSoc: 100 },
};

const REMAINING_GROUP = {
  startHour: 0, startMinute: 0, endHour: 23, endMinute: 59,
  enable: 1, workMode: 'SelfUse',
  extraParam: { minSocOnGrid: 10, fdSoc: 10, fdPwr: 0, maxSoc: 100 },
};

describe('Add remaining slot button', () => {
  function openModal(card) {
    card.shadowRoot.querySelector('.edit-btn').click();
  }

  it('shows button in edit modal when no remaining slot exists', () => {
    const card = mountCard(makeHassForRemaining([NORMAL_GROUP]));
    openModal(card);
    expect(card.shadowRoot.querySelector('.add-remaining-btn')).not.toBeNull();
  });

  it('does not show button in edit modal when a remaining slot exists', () => {
    const card = mountCard(makeHassForRemaining([NORMAL_GROUP, REMAINING_GROUP]));
    openModal(card);
    expect(card.shadowRoot.querySelector('.add-remaining-btn')).toBeNull();
  });

  it('shows button in edit modal when schedule is empty', () => {
    const card = mountCard(makeHassForRemaining([]));
    openModal(card);
    expect(card.shadowRoot.querySelector('.add-remaining-btn')).not.toBeNull();
  });

  it('button is not shown in the read-only card view', () => {
    const card = mountCard(makeHassForRemaining([NORMAL_GROUP]));
    expect(card.shadowRoot.querySelector('.add-remaining-btn')).toBeNull();
  });

  it('clicking the button adds remaining slot and stays in modal', () => {
    const card = mountCard(makeHassForRemaining([NORMAL_GROUP]));
    openModal(card);
    card.shadowRoot.querySelector('.add-remaining-btn').click();
    expect(card.shadowRoot.querySelector('dialog').open).toBe(true);
  });

  it('new remaining slot has SelfUse work mode', () => {
    const card = mountCard(makeHassForRemaining([NORMAL_GROUP]));
    openModal(card);
    card.shadowRoot.querySelector('.add-remaining-btn').click();
    const remaining = card._editGroups.find(g => g.startMins === 0 && g.endMins === 1439);
    expect(remaining).toBeDefined();
    expect(remaining.workMode).toBe('SelfUse');
  });

  it('new remaining slot minSocOnGrid matches min_soc attribute', () => {
    const card = mountCard(makeHassForRemaining([NORMAL_GROUP], 15));
    openModal(card);
    card.shadowRoot.querySelector('.add-remaining-btn').click();
    const remaining = card._editGroups.find(g => g.startMins === 0 && g.endMins === 1439);
    expect(remaining.minSocOnGrid).toBe(15);
  });

  it('new remaining slot maxSoc is 100', () => {
    const card = mountCard(makeHassForRemaining([NORMAL_GROUP], 20));
    openModal(card);
    card.shadowRoot.querySelector('.add-remaining-btn').click();
    const remaining = card._editGroups.find(g => g.startMins === 0 && g.endMins === 1439);
    expect(remaining.maxSoc).toBe(100);
  });

  it('existing groups are preserved alongside new remaining slot', () => {
    const card = mountCard(makeHassForRemaining([NORMAL_GROUP]));
    openModal(card);
    card.shadowRoot.querySelector('.add-remaining-btn').click();
    expect(card._editGroups).toHaveLength(2);
  });

  it('defaults minSocOnGrid to 10 when min_soc attribute is absent', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 90, fdPwr: 0, maxSoc: 100 })]));
    openModal(card);
    card.shadowRoot.querySelector('.add-remaining-btn').click();
    const remaining = card._editGroups.find(g => g.startMins === 0 && g.endMins === 1439);
    expect(remaining.minSocOnGrid).toBe(10);
  });

  it('delete button is present on the remaining slot row', () => {
    const card = mountCard(makeHassForRemaining([NORMAL_GROUP, REMAINING_GROUP]));
    openModal(card);
    const remainingIdx = card._editGroups.findIndex(g => g.startMins === 0 && g.endMins === 1439);
    expect(card.shadowRoot.querySelector(`.del-btn[data-idx="${remainingIdx}"]`)).not.toBeNull();
  });

  it('deleting the remaining slot removes it from editGroups', () => {
    const card = mountCard(makeHassForRemaining([NORMAL_GROUP, REMAINING_GROUP]));
    openModal(card);
    const remainingIdx = card._editGroups.findIndex(g => g.startMins === 0 && g.endMins === 1439);
    card.shadowRoot.querySelector(`.del-btn[data-idx="${remainingIdx}"]`).click();
    expect(card._editGroups.find(g => g.startMins === 0 && g.endMins === 1439)).toBeUndefined();
  });
});

// ---------------------------------------------------------------------------
// Save payload
// ---------------------------------------------------------------------------

describe('Max SoC - save payload', () => {
  it('includes maxSoc in extraParam when saving', async () => {
    const send = vi.fn().mockResolvedValue({ ok: true });
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 80 })], send));
    card.shadowRoot.querySelector('.edit-btn').click();
    card.shadowRoot.querySelector('.save-btn').click();
    await tick();
    expect(send).toHaveBeenCalledWith(
      expect.objectContaining({
        type: 'foxess/save_schedule',
        groups: expect.arrayContaining([
          expect.objectContaining({
            extraParam: expect.objectContaining({ maxSoc: 80 }),
          }),
        ]),
      })
    );
  });

});
